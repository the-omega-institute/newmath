import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntermediateValueBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntermediateValueBisectionCarrier [AskSetup] [PackageSetup]
    (locatedInterval rationalCells dyadicBranch signLedger streamWindows regularReadback
      realSeal transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory locatedInterval ∧ UnaryHistory rationalCells ∧ UnaryHistory dyadicBranch ∧
    UnaryHistory signLedger ∧ UnaryHistory streamWindows ∧ UnaryHistory regularReadback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧
          Cont locatedInterval rationalCells dyadicBranch ∧
            Cont dyadicBranch signLedger streamWindows ∧
              Cont streamWindows regularReadback realSeal ∧
                Cont transport replay provenance ∧ PkgSig bundle realSeal pkg

theorem IntermediateValueBisectionCarrier_sign_ledger_stability [AskSetup] [PackageSetup]
    {locatedInterval rationalCells dyadicBranch signLedger streamWindows regularReadback
      realSeal transport replay provenance nameRow transportedSign : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueBisectionCarrier locatedInterval rationalCells dyadicBranch signLedger
        streamWindows regularReadback realSeal transport replay provenance nameRow bundle pkg ->
      Cont dyadicBranch signLedger streamWindows ->
        hsame transportedSign signLedger ->
          PkgSig bundle realSeal pkg ->
            UnaryHistory transportedSign ∧ UnaryHistory streamWindows ∧
              SemanticNameCert
                (fun row : BHist => hsame row streamWindows ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row signLedger ∨ hsame row transportedSign ∨ hsame row streamWindows)
                (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row streamWindows)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert
  intro carrier branchSignWindows transportedSame realSealPkg
  obtain ⟨_locatedUnary, _rationalUnary, dyadicUnary, signUnary, streamUnary,
    _regularUnary, _realUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _locatedRationalBranch, _carrierBranchSignWindows,
    _streamRegularSeal, _transportReplayProvenance, _carrierPkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedSign :=
    unary_transport_symm signUnary transportedSame
  have streamWindowsUnary : UnaryHistory streamWindows :=
    unary_cont_closed dyadicUnary signUnary branchSignWindows
  have sourceStream :
      (fun row : BHist => hsame row streamWindows ∧ UnaryHistory row) streamWindows := by
    exact ⟨hsame_refl streamWindows, streamWindowsUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row streamWindows ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row signLedger ∨ hsame row transportedSign ∨ hsame row streamWindows)
        (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row streamWindows)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro streamWindows sourceStream
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨realSealPkg, source.left⟩
    }
  exact ⟨transportedUnary, streamWindowsUnary, cert⟩

end BEDC.Derived.IntermediateValueBisectionUp
