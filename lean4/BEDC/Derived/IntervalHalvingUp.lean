import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalHalvingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalHalvingCarrier [AskSetup] [PackageSetup]
    (left right midpoint chosenHalf radius streamWindow regularReadback realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory midpoint ∧ UnaryHistory chosenHalf ∧
    UnaryHistory radius ∧ UnaryHistory streamWindow ∧ UnaryHistory regularReadback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ hsame transport (append left right) ∧
        Cont left right midpoint ∧ Cont midpoint chosenHalf radius ∧
          Cont radius streamWindow regularReadback ∧ Cont regularReadback realSeal replay ∧
            Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem IntervalHalvingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {left right midpoint chosenHalf radius streamWindow regularReadback realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalHalvingCarrier left right midpoint chosenHalf radius streamWindow regularReadback
        realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row midpoint ∨ hsame row chosenHalf ∨
              hsame row radius ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row realSeal ∧ Cont regularReadback realSeal replay ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame ∧
        Cont left right midpoint ∧ Cont midpoint chosenHalf radius ∧
          Cont radius streamWindow regularReadback ∧ Cont regularReadback realSeal replay ∧
            hsame transport (append left right) ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_leftUnary, _rightUnary, _midpointUnary, _chosenHalfUnary, _radiusUnary,
      _streamWindowUnary, _regularReadbackUnary, realSealUnary, _transportUnary,
      transportAnchor, midpointRoute, radiusRoute, readbackRoute, realSealRoute,
      provenanceRoute, packageRoute⟩ := carrier
  have sourceAtSeal : hsame realSeal realSeal ∧ UnaryHistory realSeal :=
    ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row midpoint ∨ hsame row chosenHalf ∨
              hsame row radius ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row realSeal ∧ Cont regularReadback realSeal replay ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceAtSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        have otherSameSeal : hsame _other realSeal :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory _other := by
          cases sameRows
          exact source.right
        exact ⟨otherSameSeal, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realSealRoute, provenanceRoute, packageRoute⟩
  }
  exact
    ⟨cert, midpointRoute, radiusRoute, readbackRoute, realSealRoute, transportAnchor,
      packageRoute⟩

end BEDC.Derived.IntervalHalvingUp
