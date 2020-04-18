const {
  Var,
  Ref,
  Typ,
  All,
  Lam,
  App,
  Let,
  Ann,
  Nil,
  Ext,
  find,
  shift,
  stringify_term,
} = require("formality-core");

const fs = require("fs");

// Parsing
// =======

// Is this a space character?
function is_space(chr) {
  return chr === " " || chr === "\t" || chr === "\n";
};

// Is this a name-valid character?
function is_name(chr) {
  var val = chr.charCodeAt(0);
  return (val >= 46 && val < 47)   // .
      || (val >= 48 && val < 58)   // 0-9
      || (val >= 65 && val < 91)   // A-Z
      || (val >= 95 && val < 96)   // _
      || (val >= 97 && val < 123); // a-z
};

// Returns the first function that doesn't throw, or null
function first_valid(fns) {
  for (var i = 0; i < fns.length; ++i) {
    try {
      return fns[i]();
    } catch (e) {
      continue;
    }
  };
  return null;
};

// Drop characters while a condition is met.
function drop_while(cond, code, indx, fmcs) {
  while (indx < code.length && cond(code[indx])) {
    fmcs += code[indx++];
  };
  return [indx, fmcs];
};

// Drop spaces
function drop_spaces(code, indx, fmcs) {
  return drop_while(is_space, code, indx, fmcs);
};

// Drops comment
function drop_comment(code, indx, fmcs) {
  var [indx, fmcs] = drop_spaces(code, indx, fmcs);
  var pref = code.slice(indx, indx + 2)
  if (pref === "//" || pref === "--") {
    while (indx < code.length && code[indx] !== "\n") {
      fmcs += code[indx++];
    }
    fmcs += code[indx++];
  }
  if (pref === "/*") {
    while (indx < code.length && code.slice(indx, indx+2) !== "*/") {
      fmcs += code[indx++];
    }
    fmcs += code[indx++];
    fmcs += code[indx++];
  }
  if (code.slice(indx, indx + 2) === "{-") {
    while (indx < code.length && code.slice(indx, indx+2) !== "-}") {
      fmcs += code[indx++];
    }
    fmcs += code[indx++];
    fmcs += code[indx++];
  }
  return [indx, fmcs];
};

// Drops spaces and comments
function next(code, indx, fmcs) {
  while (true) {
    var [new_indx, new_fmcs] = drop_comment(code, indx, fmcs);
    if (new_indx === indx) {
      return [indx, fmcs];
    } else {
      indx = new_indx;
      fmcs = new_fmcs;
    }
  };
};

// Drops spaces and parses an exact string
function parse_str(code, indx, fmcs, str) {
  if (str.length === 0) {
    return [indx, fmcs, str];
  } else if (indx < code.length && code[indx] === str[0]) {
    return parse_str(code, indx+1, fmcs+code[indx], str.slice(1));
  } else {
    throw "Expected `" + str + "`, found `" + code.slice(indx,indx+16) + "`.";
  };
};

// Parses one of two strings
function parse_opt(code, indx, fmcs, ch0, ch1) {
  try {
    var [indx, fmcs, str] = parse_str(code, indx, fmcs, ch0);
    return [indx, fmcs, false];
  } catch (e) {
    var [indx, fmcs, str] = parse_str(code, indx, fmcs, ch1);
    return [indx, fmcs, true];
  }
};

// Parses one of two strings
function parse_may(code, indx, fmcs, str) {
  try {
    var [indx, fmcs, skip] = parse_str(code, indx, fmcs, str);
    return [indx, fmcs, true];
  } catch (e) {
    return [indx, fmcs, false];
  }
};

// Parses a valid name, non-empty
function parse_nam(code, indx, fmcs, size = 0) {
  if (indx < code.length && is_name(code[indx])) {
    var head = code[indx];
    var [indx, fmcs, tail] = parse_nam(code, indx + 1, fmcs+code[indx], size + 1);
    return [indx, fmcs, head + tail];
  } else if (size > 0) {
    return [indx, fmcs, ""];
  } else {
    throw "Invalid name.";
  }
};

// Parses a parenthesis, `(<term>)`
function parse_par(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "(");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, term] = parse_term(code, indx, fmcs, vars);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, ")");
  return [indx, fmcs, term];
};

// Parses a dependent function type, `(<name> : <term>) -> <term>`
function parse_all(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var from               = indx;
  var [indx, fmcs, self] = parse_nam(code, indx, fmcs, 1);
  var [indx, fmcs, eras] = parse_opt(code, indx, fmcs, "(", "<");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, name] = parse_nam(code, indx, fmcs, 1);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, ":");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, bind] = parse_term(code, indx, fmcs, Ext(self, vars));
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, eras ? ">" : ")")
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "->");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, body] = parse_term(code, indx, fmcs, Ext(name, Ext(self, vars)));
  return [indx, fmcs, All(eras, self, name, bind, body, {from,to:indx})];
};

// Parses a dependent function value, `(<name>) => <term>`
function parse_lam(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var from               = indx;
  var [indx, fmcs, eras] = parse_opt(code, indx, fmcs, "(", "<");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, name] = parse_nam(code, indx, fmcs, 1);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, eras ? ">" : ")")
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, body] = parse_term(code, indx, fmcs, Ext(name, vars));
  return [indx, fmcs, Lam(eras, name, body, {from,to:indx})];
};

// Parses a local definition, `let x = val; body`
function parse_let(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var from               = indx;
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "let ");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, name] = parse_nam(code, indx, fmcs);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "=");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, expr] = parse_term(code, indx, fmcs, vars);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, body] = parse_term(code, indx, fmcs, Ext(name, vars));
  return [indx, fmcs, Let(name, expr, body, {from,to:indx})];
};

// Parses the type of types, `Type`
function parse_typ(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var from               = indx;
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "Type");
  return [indx, fmcs, Typ({from,to:indx})];
};

// Parses variables, `<name>`
function parse_var(code, indx, fmcs, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var from               = indx;
  var [indx, fmcs, name] = parse_nam(code, indx, fmcs);
  var got = find(vars, (x,i) => x === name);
  if (got) {
    return [indx, fmcs, Var(got.index, {from,to:indx})];
  } else if (!isNaN(Number(name))) {
    return [indx, fmcs, Var(Number(name), {from,to:indx})];
  } else {
    return [indx, fmcs, Ref(name, {from,to:indx})];
  };
};

// Parses a single-line application, `<term>(<term>)`
function parse_app(code, indx, fmcs, from, func, vars) {
  var [indx, fmcs, eras] = parse_opt(code, indx, fmcs, "(", "<");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, argm] = parse_term(code, indx, fmcs, vars);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, eras ? ">" : ")");
  return [indx, fmcs, App(eras, func, argm, {from,to:indx})];
};

// Parses a multi-line application, `<term> | <term>;`
function parse_pip(code, indx, fmcs, from, func, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "|");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, argm] = parse_term(code, indx, fmcs, vars);
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, ";");
  return [indx, fmcs, App(false, func, argm, {from,to:indx})];
};

// Parses a non-dependent function type, `<term> -> <term>`
function parse_arr(code, indx, fmcs, from, bind, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "->");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, body] = parse_term(code, indx, fmcs, Ext("", Ext("", vars)));
  return [indx, fmcs, All(false, "", "", shift(bind,1,0), body, {from,to:indx})];
};

// Parses an annotation, `<term> :: <term>`
function parse_ann(code, indx, fmcs, from, expr, vars) {
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, skip] = parse_str(code, indx, fmcs, "::");
  var [indx, fmcs      ] = next(code, indx, fmcs);
  var [indx, fmcs, type] = parse_term(code, indx, fmcs, vars);
  return [indx, fmcs, Ann(false, expr, type, {from,to:indx})];
};

// #1 -> Nat.succ(Nat.zero)
function parse_nat(code, indx, fmcs, vars) {
  var [indx, fmcs       ] = next(code, indx, fmcs);
  var [indx, _    , skip] = parse_str(code, indx, fmcs, "#");
  var [indx, _          ] = next(code, indx, fmcs);
  var [indx, _    , name] = parse_nam(code, indx, fmcs);
  var numb = Number(name);
  if (isNaN(numb)) {
    throw "";
  } else {
    var code = "Nat.zero";
    var term = Ref("Nat.zero");
    for (var i = 0; i < numb; ++i) {
      term = App(false, Ref("Nat.succ"), term);
      code = "Nat.succ(" + code + ")";
    }
    fmcs += code;
    return [indx, fmcs, term];
  }
};

// Parses a term
function parse_term(code, indx = 0, fmcs, vars = Nil()) {
  var [indx, fmcs] = next(code, indx, fmcs);
  var from = indx;

  // Parses the base term, trying each variant once
  var base_parse = first_valid([
    () => parse_all(code, indx, fmcs, vars),
    () => parse_lam(code, indx, fmcs, vars),
    () => parse_let(code, indx, fmcs, vars),
    () => parse_par(code, indx, fmcs, vars),
    () => parse_typ(code, indx, fmcs, vars),
    () => parse_nat(code, indx, fmcs, vars),
    () => parse_var(code, indx, fmcs, vars),
  ]);

  // Parses postfix extensions, trying each variant repeatedly
  var post_parse = base_parse;
  while (true) {
    var [indx, fmcs, term] = post_parse;
    post_parse = first_valid([
      () => parse_app(code, indx, fmcs, from, term, vars),
      () => parse_pip(code, indx, fmcs, from, term, vars),
      () => parse_arr(code, indx, fmcs, from, term, vars),
      () => parse_ann(code, indx, fmcs, from, term, vars),
    ]);
    if (!post_parse) {
      return base_parse;
    } else {
      base_parse = post_parse;
    }
  }

  return null;
};

// Parses a file
function parse_defs(code, indx = 0, file) {
  var form = "";
  var defs = {};
  function parse_defs(code, indx) {
    try {
      var [indx, fmcs      ] = next(code, indx, form);
      var [indx, fmcs, name] = parse_nam(code, indx, fmcs);
      var [indx, fmcs      ] = next(code, indx, fmcs);
      var [indx, fmcs, skip] = parse_str(code, indx, fmcs, ":");
      var [indx, fmcs      ] = next(code, indx, fmcs);
      var [indx, fmcs, type] = parse_term(code, indx, fmcs, Nil());
      var [indx, fmcs      ] = drop_spaces(code, indx, fmcs);
      var [indx, fmcs, loop] = parse_may(code, indx, fmcs, "//loop//");
      var [indx, fmcs      ] = drop_spaces(code, indx, fmcs);
      var [indx, fmcs, prim] = parse_may(code, indx, fmcs, "//prim//");
      var [indx, fmcs      ] = next(code, indx, fmcs);
      var [indx, fmcs, term] = parse_term(code, indx, fmcs, Nil());
      defs[name] = {type, term, meta: {loop,prim}};
      form += fmcs;
      parse_defs(code, indx);
    } catch (e) { }
  }
  parse_defs(code, indx);
  fs.writeFileSync(file+"c", form);
  //console.log(code);
  //console.log("form:",form);
  //console.log("-------------------");
  return defs;
};

module.exports = {parse_defs};
