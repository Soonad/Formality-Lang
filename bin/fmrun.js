#!/usr/bin/env node

var parse_defs = require("./../FormalityLang.js").parse_defs;
require("formality-core/bin/lib.js").run(process.argv[2], ".", ".fm", parse_defs);
