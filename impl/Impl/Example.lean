import Impl.TypeCheck
import Impl.Semantics
import Impl.Macro

def simple :=
  [lang| for i : 0 .. 1 in 1.0]
#eval Typecheck.term [] simple
#eval Semantics.normalize simple

def simpleIndex :=
  [lang| (for i : 0 .. 1 in 1.0)[0]]
#eval Typecheck.term [] simpleIndex
#eval Semantics.normalize simpleIndex

def twoD :=
  [lang| for i : 0 .. 5 in for j : 0 .. 5 in 1.0]
#eval Typecheck.term [] twoD
#eval Semantics.normalize twoD

def twoDIndex :=
  [lang| (for i : 0 .. 5 in for j : 0 .. 5 in 1.0)[2][3]]
#eval Typecheck.term [] twoDIndex
#eval Semantics.normalize twoDIndex


def matMul :=
  [lang|
    let A = for i : 0 .. 1  in
      for j : 0 .. 1 in
        1.0
    in let B = for i : 0 .. 1 in
      for j : 0 .. 1 in
        2.0
    in for i : 0 .. 1 in
      for j : 0 .. 1 in
        A[i][j] * B[j][i]
  ]
#eval Typecheck.term [] matMul
#eval Semantics.normalize matMul

def matMulIndex :=
  [lang|
    (let A = for i : 0 .. 1  in
      for j : 0 .. 1 in
        1.0
    in let B = for i : 0 .. 1 in
      for j : 0 .. 1 in
        2.0
    in for i : 0 .. 1 in
      for j : 0 .. 1 in
        A[i][j] * B[j][i])[0][0]
  ]
#eval Typecheck.term [] matMulIndex
#eval Semantics.normalize matMulIndex
