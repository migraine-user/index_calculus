import Impl.Syntax

declare_syntax_cat range

syntax num ".." num : range

syntax "empty" : range

declare_syntax_cat data_type

syntax "float" : data_type
syntax  data_type "×" data_type  : data_type
syntax num "." data_type : data_type
syntax data_type:60 "->" data_type:61 : data_type
syntax "("data_type")":data_type

declare_syntax_cat _term

syntax "("_term")":_term

syntax scientific: _term

syntax num: _term

syntax "for" ident ":" range " in " _term : _term

syntax "let" ident "=" _term " in " _term : _term

syntax "(" _term "," _term ")" : _term

syntax "if" _term "<=" _term "then" _term "else" _term : _term

syntax _term " + " _term: _term
syntax _term " - " _term: _term
syntax _term " * " _term: _term
syntax _term " / " _term: _term

syntax "λ" "(" ident ":" data_type ")" "." _term : _term

syntax _term _term : _term

syntax ident: _term

syntax _term "[" _term "]" : _term

syntax _term ".fst" : _term

syntax _term ".snd" : _term

syntax "[data_type|" data_type "]" : term
macro_rules
  | `([data_type| float]) => `(Syntax.DataTy.float)
  | `([data_type| $a:data_type ×  $b:data_type]) =>
      `(Syntax.DataTy.tuple [data_type| $a] [data_type| $b])
  | `([data_type| $n:num . $ty:data_type]) =>
      `(Syntax.DataTy.array $n [data_type| $ty])
  | `([data_type| $a:data_type -> $b:data_type]) =>
      `(Syntax.DataTy.func [data_type|$a] [data_type|$b])
  | `([data_type| ($a)]) => `([data_type|$a])

syntax "[range|" range "]" : term
macro_rules
  | `([range| $a:num .. $b:num]) => `(Syntax.Range.range $a $b)
  | `([range| empty]) => `(Syntax.Range.empty)

syntax "[ident|" ident "]" : term
macro_rules
  | `([ident| $x:ident]) => `(Syntax.Ident.ident $(Lean.quote x.getId.toString))

syntax "[lang|" _term "]" : term
macro_rules
  | `([lang| ($t)]) => `([lang| $t])
  | `([lang| $x: scientific ]) => `(Syntax.Term.floatLit $x)
  | `([lang| $n: num]) => `(Syntax.Term.natLit $n)
  | `([lang| for $i:ident : $r:range in $t:_term]) =>
      `(Syntax.Term.for_
        [ident| $i]
        [range| $r]
        [lang| $t])
  | `([lang| let $x:ident = $t:_term in $in_t:_term]) =>
      `(Syntax.Term.let_
        [ident| $x]
        [lang| $t]
        [lang| $in_t])
  | `([lang| ( $a , $b )]) =>
      `(Syntax.Term.tuple
        [lang| $a]
        [lang| $b])
  | `([lang| if $lhs <= $rhs then $if_body else $else_body]) =>
      `(Syntax.Term.ternary
          (Syntax.Leq.leq [lang| $lhs] [lang| $rhs])
          [lang| $if_body]
          [lang| $else_body])
  | `([lang| $a + $b]) => `(Syntax.Term.binary [lang| $a] Syntax.Arith.plus [lang| $b])
  | `([lang| $a - $b]) => `(Syntax.Term.binary [lang| $a] Syntax.Arith.minus [lang| $b])
  | `([lang| $a * $b]) => `(Syntax.Term.binary [lang| $a] Syntax.Arith.times [lang| $b])
  | `([lang| $a / $b]) => `(Syntax.Term.binary [lang| $a] Syntax.Arith.divide [lang| $b])
  | `([lang| λ ($x:ident : $ty:data_type). $t ]) =>
      `(Syntax.Term.abs [ident| $x] [data_type| $ty] [lang| $t])
  | `([lang| $a $b]) =>
      `(Syntax.Term.app [lang| $a] [lang| $b])
  | `([lang| $i:ident ]) => `(Syntax.Term.var [ident| $i] )
  | `([lang| $arr[$i]]) => `(Syntax.Term.index [lang| $arr] [lang| $i])
