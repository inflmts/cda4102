if exists("b:current_syntax")
  finish
endif
let b:current_syntax = "prabhat"

syn match Statement /^.\+\n\~\+$/
syn match Comment /^vim:.*/
syn match Title /\%1l.*/

syn sync minlines=1 linebreaks=1
