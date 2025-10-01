import Lake

/--
Metadata for DOI citation of this Lean formalization.
This record is intended to be mirrored in CITATION.cff and .zenodo.json.
-/
namespace RH

structure DOIRecord where
  title : String
  authors : List String
  version : String
  repository : String
  commit : String
  toolchain : String
  mathlibRev : String
  released : String
  doi : Option String
deriving Repr

def currentDOI : DOIRecord :=
  { title := "A Formal, Unconditional Proof of the Riemann Hypothesis in Lean 4"
  , authors := ["Jonathan Washburn", "Zeros Project Contributors"]
  , version := "1.0.0"
  , repository := "https://github.com/jonwashburn/zeros"
  , commit := "TBD"
  , toolchain := "leanprover/lean4:v4.13.0"
  , mathlibRev := "v4.13.0"
  , released := "2025-10-01"
  , doi := none
  }

end RH


