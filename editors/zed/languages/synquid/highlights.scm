; Synquid (.sq) syntax highlighting.

; keywords
[
  "data" "measure" "termination" "predicate" "qualifier" "mutual" "inline" "type"
  "let" "in" "match" "with" "where" "if" "then" "else" "error"
] @keyword

["True" "False"] @boolean
["Bool" "Int" "Set"] @type.builtin

; structural operators
"::" @operator
"->" @operator
"=" @operator
"|" @operator
"<" @operator
">" @operator
"\\" @operator

; identifier classes
(constructor) @constructor
(variable) @variable
(special_var) @variable.special
(special_index) @variable.special
(wildcard) @variable.special

(integer) @number
(operator) @operator
(hole) @constant

(comment_line) @comment
(comment_block) @comment

; punctuation
"(" @punctuation.bracket
")" @punctuation.bracket
"[" @punctuation.bracket
"]" @punctuation.bracket
"{" @punctuation.bracket
"}" @punctuation.bracket
"," @punctuation.delimiter
"." @punctuation.delimiter

; structural scopes — fire where declarations parse without being swallowed
(function_signature name: (variable) @function)
(function_definition name: (variable) @function)
(measure_declaration name: (variable) @function)
(predicate_declaration name: (variable) @function)
(inline_declaration name: (variable) @function)
(mutual_declaration name: (variable) @function)
(type_alias name: (constructor) @type)
(data_declaration name: (constructor) @type)
