import BEDC.Derived.CauchyNetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyNetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyNetCarrier [AskSetup] [PackageSetup]
    (directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory directed ∧ UnaryHistory schedule ∧ UnaryHistory regseq ∧
    UnaryHistory dyadic ∧ UnaryHistory classifier ∧ UnaryHistory realHandoff ∧
      UnaryHistory nameRow ∧ Cont directed schedule regseq ∧
        Cont classifier realHandoff route ∧ Cont route transport provenance ∧
          PkgSig bundle provenance pkg

theorem CauchyNetCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {directed schedule regseq dyadic classifier realHandoff transport route provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport route
        provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport
              route provenance nameRow bundle pkg ∧ hsame row realHandoff)
          (fun row : BHist => hsame row classifier ∨ hsame row realHandoff)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row realHandoff)
          hsame ∧
        UnaryHistory classifier ∧ UnaryHistory realHandoff ∧
          Cont directed schedule regseq ∧ Cont classifier realHandoff route ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierSurface := carrier
  obtain ⟨_directedUnary, _scheduleUnary, _regseqUnary, _dyadicUnary, classifierUnary,
    realHandoffUnary, _nameRowUnary, directedScheduleRegseq, classifierRealRoute,
    _routeTransportProvenance, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CauchyNetCarrier directed schedule regseq dyadic classifier realHandoff transport
            route provenance nameRow bundle pkg ∧ hsame row realHandoff)
        (fun row : BHist => hsame row classifier ∨ hsame row realHandoff)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row realHandoff)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realHandoff ⟨carrierSurface, hsame_refl realHandoff⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr source.right
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, source.right⟩
    }
  exact
    ⟨cert, classifierUnary, realHandoffUnary, directedScheduleRegseq, classifierRealRoute,
      provenancePkg⟩

end BEDC.Derived.CauchyNetUp
