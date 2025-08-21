import Impl.Elab

def diag2 :=
  (lang|
    for i: 0⋯1 in
      for j: 0⋯1 in
        if i ≤ 0 then
          -- i = 0
          if j ≤ 0 then
            -- j = 0
            1.0
          else
            0.0
        else if i ≤ 1 then
          -- i = 1
          if j ≤ 1 then
            if j ≤ 0 then
              0.0
            else
              -- j = 1
              1.0
          else
            0.0
        else
          0.0
  )
#eval typecheck diag2
#eval run diag2

def matMul2 := (lang|
  let A := for i : 0⋯1 in
    for j : 0⋯1 in
      if i ≤ 0 then
        1.0 * 2.0 - 3.0
      else if j ≤ 1 then
        2.0
      else
        3.0
  in let B := for i : 0⋯1 in
    for j : 0⋯1 in
      if j ≤ 1 then
        if i ≤ 1 then
          9.0 * A[j][i] - 12.5
        else
          8.0
      else
        7.0
  in for i : 0⋯1 in
    for j : 0⋯1 in
      A[i][j] * B[j][i]
)
#eval typecheck matMul2
#eval run matMul2

def emptee := (lang|
  for i : empty in
    for j : empty in
      0.1
)
-- The runtime value doesn't exactly match the type!
-- doesn't matter bc it is never indexed at runtime.
#eval typecheck emptee
#eval run emptee

def empteeError := (lang|
  let A := for i : empty in 1.0
  in A[0]
)
#eval typecheck empteeError
#eval run empteeError

def empteeNotError := (lang|
  let A := for i : empty in 1.0
  in for j : empty in A[j]
)
#eval typecheck empteeNotError
#eval run empteeNotError

def empteeEdgecase := (lang|
  let A := for i : empty in 1.0
  in for j : 0⋯0 in A
)
#eval typecheck empteeEdgecase
#eval run empteeEdgecase
