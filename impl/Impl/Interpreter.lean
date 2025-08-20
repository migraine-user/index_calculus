import Impl.TypeCheck
inductive RunVal: Type
| float (f:Float)
| nat : Nat -> RunVal
| array (arr: List RunVal)
| tuple (fst:RunVal)(snd:RunVal)
deriving Repr
instance : Repr RunVal where
  reprPrec x prec :=
    let s := Repr.reprPrec x prec |> toString  -- calls the derived one internally
    let kill enemy := fun s =>
      s.replace enemy ""
    s |> kill "RunVal.array" |> kill "RunVal.tuple" |> kill "RunVal.float"
abbrev RunResult := Except String RunVal

def RunEnv := List (Ident × RunVal)
mutual
def run(env: RunEnv)(t:Term) : RunResult :=
  match t with
  | .floatLit f => .ok $ .float f
  | .natLit n => .ok $ .nat n
  | .let_ id t inT => do
    let v <- run env t
    let env' := (id,v)::env
    run env' inT
  | .place p => match p with
    | .ident i =>
      match env.find? (fun (id,val) => if id == i then true else false) with
      | .none => .error "identifier not defined"
      | .some (id,v) => .ok v
    | .index ⟨t,idx⟩ => do
      let v <- run env (.place t)
      let i <- run env idx
      let i:RunVal <- match i with
      | .nat n => .ok $ i
      | _ => .error "index must be a natural number"
      let v <- match v with
      | .array a => .ok $ v
      | _ => .error "cannot index a non-array"
      match (v,i) with
      | (.array a, .nat i) =>
        match a[i]? with
        | .some v => .ok v
        | .none => .error "index out of bounds"
      | _ => .error "should be unreachable"
    | .fst tup => do
      let tup <- run env $ .place tup
      match tup with
      | .tuple fst snd => .ok fst
      | _ => .error "accessing a non tuple like tuple"
    | .snd tup => do
      let tup <- run env $ .place tup
      match tup with
      | .tuple fst snd => .ok snd
      | _ => .error "accessing a non tuple like tuple"
  | .for_ i r body => match r with
    | .empty => .ok $ .array []
    | .range l r => do
    let rng := List.range' l (r-l+1)
    let runMap := fun n =>
      run ((i,.nat n)::env) body
    let results := (List.map runMap rng)
    let vals := results.foldr (fun (r: RunResult) (acc: Except String (List RunVal) ) =>
      match r, acc with
      | .ok x, .ok xs => .ok $ x::xs
      | .error e, _ => .error e
      | _, _ => .error "should be unreachable") (.ok [])
    match vals with
    | .ok lst => .ok $ .array lst
    | .error e => .error e
  | .tuple fst snd => do
    let fst <- run env fst
    let snd <- run env snd
    return .tuple fst snd
  | .ternary (.leq i j) bodyIf bodyElse => do
    let i <- match env.find? (fun (id,val) => if id == i then true else false) with
      | .none => .error "identifier not defined"
      | .some (id,v) => .ok v
    let j <- run env j
    match (i, j) with
    | (.nat i, .nat j) => if i <= j then run env bodyIf else run env bodyElse
    | _ => .error "shit"
  | .binary lhs op rhs => do
    let lhs <- run env lhs
    let rhs <- run env rhs
    match (lhs, rhs) with
    | (.float lhs, .float rhs) => .ok $ .float $ match op with
      | .plus => lhs + rhs
      | .minus => lhs - rhs
      | .times => lhs * rhs
      | .divide => lhs / rhs
    | _ => .error "binary op on non-floats"
end
