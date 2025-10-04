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

def ifElse := [lang|
  for i:0 .. 1 in
    if i <= 0 then
      0.0
    else
      1.1]
#eval Typecheck.term [] ifElse
#eval Semantics.normalize ifElse

def ifElse0 := [lang|
  (for i:0 .. 1 in
    if i <= 0 then
      0.0
    else
      1.1)[0]]
#eval Typecheck.term [] ifElse0
#eval Semantics.normalize ifElse0


def diag2 := [lang|
  for i:0 .. 1 in
    for j:0 .. 2 in
      if i <= 0 then
        if j <= 0 then
          1.0
        else
          0.0
      else if i <= 1 then
        if j <= 1 then
          if j <= 0 then
            0.0
          else
            1.0
        else
          0.0
      else
        0.0]
#eval Typecheck.term [] diag2
#eval Semantics.normalize diag2

def diag2index := [lang|
  (for i:0 .. 1 in
    for j:0 .. 2 in
      if i <= 0 then
        if j <= 0 then
          1.0
        else
          0.0
      else if i <= 1 then
        if j <= 1 then
          if j <= 0 then
            0.0
          else
            1.0
        else
          0.0
      else
        0.0)[0][0]]
#eval Typecheck.term [] diag2index
#eval Semantics.normalize diag2index

def func := [lang|
  λ(arr:5 . 5 . float × float). arr[3]
]
#eval Typecheck.term [] func

def func_app := [lang|
  let f = λ(arr:5 . 5 . float × float). arr[3][3]
  in f (for i: 0 .. 10 in for j: 0 .. 10 in (1.0 , 1.0))
]
#eval Typecheck.term [] func_app
#eval Semantics.normalize func_app
