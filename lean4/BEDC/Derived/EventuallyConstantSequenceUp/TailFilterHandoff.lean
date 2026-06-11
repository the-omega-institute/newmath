import BEDC.Derived.EventuallyConstantSequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EventuallyConstantSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EventuallyConstantSequenceCarrier [AskSetup] [PackageSetup]
    (S T F R L A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory R ∧
    UnaryHistory L ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S T F ∧ Cont F R L ∧
        Cont L A H ∧ Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EventuallyConstantSequenceTailFilterHandoff [AskSetup] [PackageSetup]
    {S T F R L A H C P N tailRead readbackRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EventuallyConstantSequenceCarrier S T F R L A H C P N bundle pkg →
      Cont S T tailRead →
        Cont tailRead R readbackRead →
          Cont readbackRead L limitRead →
            PkgSig bundle limitRead pkg →
              SemanticNameCert
                (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row T ∨ hsame row F ∨ hsame row R ∨
                    hsame row L ∨ hsame row A ∨ hsame row limitRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont S T tailRead ∧
                    Cont tailRead R readbackRead ∧ Cont readbackRead L limitRead ∧
                      PkgSig bundle limitRead pkg)
                hsame ∧ UnaryHistory tailRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier tailRoute readbackRoute limitRoute limitPkg
  obtain ⟨SUnary, TUnary, _FUnary, RUnary, LUnary, _AUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _tailBaseRoute, _limitBaseRoute, _sealBaseRoute,
    _provenanceRoute, _provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed SUnary TUnary tailRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed tailUnary RUnary readbackRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed readbackUnary LUnary limitRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row T ∨ hsame row F ∨ hsame row R ∨
            hsame row L ∨ hsame row A ∨ hsame row limitRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S T tailRead ∧ Cont tailRead R readbackRead ∧
            Cont readbackRead L limitRead ∧ PkgSig bundle limitRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRead ⟨hsame_refl limitRead, limitUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, readbackRoute, limitRoute, limitPkg⟩
  }
  exact ⟨cert, tailUnary, readbackUnary, limitUnary⟩

end BEDC.Derived.EventuallyConstantSequenceUp
