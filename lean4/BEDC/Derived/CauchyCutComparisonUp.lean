import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCutComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCutComparisonCarrier [AskSetup] [PackageSetup]
    (cutSide setoidSide synchronizedWindow regularReadback dyadicTolerance realSeal
      transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory cutSide ∧ UnaryHistory setoidSide ∧ UnaryHistory regularReadback ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont cutSide setoidSide synchronizedWindow ∧
        Cont synchronizedWindow regularReadback dyadicTolerance ∧
          Cont dyadicTolerance transport realSeal ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem CauchyCutComparisonCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K Q S R D A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCutComparisonCarrier K Q S R D A H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row A ∧ CauchyCutComparisonCarrier K Q S R D A H C P N bundle pkg)
          (fun row : BHist =>
            hsame row K ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ Cont K Q S ∨ Cont S R D)
          (fun row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row A)
          hsame ∧
        UnaryHistory A ∧ Cont K Q S ∧ Cont S R D ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨cutUnary, setoidUnary, readbackUnary, transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, cutSetoidWindow, windowReadbackDyadic,
    dyadicTransportSeal, provenancePkg, localNamePkg⟩ := carrier
  have windowUnary : UnaryHistory S :=
    unary_cont_closed cutUnary setoidUnary cutSetoidWindow
  have dyadicUnary : UnaryHistory D :=
    unary_cont_closed windowUnary readbackUnary windowReadbackDyadic
  have sealUnary : UnaryHistory A :=
    unary_cont_closed dyadicUnary transportUnary dyadicTransportSeal
  have carrierAtSeal :
      CauchyCutComparisonCarrier K Q S R D A H C P N bundle pkg :=
    ⟨cutUnary, setoidUnary, readbackUnary, transportUnary, _replayUnary, _provenanceUnary,
      _localNameUnary, cutSetoidWindow, windowReadbackDyadic, dyadicTransportSeal,
      provenancePkg, localNamePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row A ∧ CauchyCutComparisonCarrier K Q S R D A H C P N bundle pkg)
          (fun row : BHist =>
            hsame row K ∨ hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ Cont K Q S ∨ Cont S R D)
          (fun row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row A)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro A ⟨hsame_refl A, carrierAtSeal⟩
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
        intro row other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl cutSetoidWindow))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact ⟨cert, sealUnary, cutSetoidWindow, windowReadbackDyadic, provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyCutComparisonUp
