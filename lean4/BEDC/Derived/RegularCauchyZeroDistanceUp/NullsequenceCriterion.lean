import BEDC.Derived.RegularCauchyZeroDistanceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyZeroDistanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyZeroDistanceCarrier [AskSetup] [PackageSetup]
    (left right difference nullSeq equality window tolerance transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory difference ∧
    UnaryHistory nullSeq ∧ UnaryHistory equality ∧ UnaryHistory window ∧
      UnaryHistory tolerance ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont window tolerance transport ∧
          Cont transport nullSeq replay ∧ PkgSig bundle provenance pkg

theorem RegularCauchyZeroDistanceNullsequenceCriterion [AskSetup] [PackageSetup]
    {left right difference nullSeq equality window tolerance transport replay provenance
      localName nullRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyZeroDistanceCarrier left right difference nullSeq equality window tolerance
        transport replay provenance localName bundle pkg ->
      Cont difference nullSeq nullRead ->
        Cont nullRead equality zeroRead ->
          PkgSig bundle zeroRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row left ∨ hsame row right ∨ hsame row difference ∨
                    hsame row nullSeq ∨ hsame row equality ∨ hsame row zeroRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont difference nullSeq nullRead ∧
                    Cont nullRead equality zeroRead ∧ PkgSig bundle zeroRead pkg ∧
                      PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory nullRead ∧ UnaryHistory zeroRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier nullRoute zeroRoute zeroPkg
  obtain
    ⟨_leftUnary, _rightUnary, differenceUnary, nullSeqUnary, equalityUnary, _windowUnary,
      _toleranceUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
      _windowToleranceRoute, _transportNullRoute, provenancePkg⟩ := carrier
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed differenceUnary nullSeqUnary nullRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed nullUnary equalityUnary zeroRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row difference ∨
              hsame row nullSeq ∨ hsame row equality ∨ hsame row zeroRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont difference nullSeq nullRead ∧
              Cont nullRead equality zeroRead ∧ PkgSig bundle zeroRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead ⟨hsame_refl zeroRead, zeroUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nullRoute, zeroRoute, zeroPkg, provenancePkg⟩
  }
  exact ⟨cert, nullUnary, zeroUnary⟩

end BEDC.Derived.RegularCauchyZeroDistanceUp
