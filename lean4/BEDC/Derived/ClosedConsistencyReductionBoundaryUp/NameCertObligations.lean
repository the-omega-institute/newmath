import BEDC.Derived.ClosedConsistencyReductionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedConsistencyReductionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedConsistencyReductionBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S Q E D K O _H _C P N sourceRoute endpointRead dischargeRead consistencyRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory Q →
        UnaryHistory E →
          UnaryHistory D →
            UnaryHistory K →
              UnaryHistory O →
                UnaryHistory N →
                  Cont S Q sourceRoute →
                    Cont sourceRoute E endpointRead →
                      Cont endpointRead D dischargeRead →
                        Cont dischargeRead K consistencyRead →
                          Cont consistencyRead O namedRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle namedRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row S ∨ hsame row Q ∨ hsame row E ∨
                                        hsame row D ∨ hsame row K ∨ hsame row O ∨
                                          hsame row sourceRoute ∨
                                            hsame row endpointRead ∨
                                              hsame row dischargeRead ∨
                                                hsame row consistencyRead ∨
                                                  hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont S Q sourceRoute ∧
                                        Cont sourceRoute E endpointRead ∧
                                          Cont endpointRead D dischargeRead ∧
                                            Cont dischargeRead K consistencyRead ∧
                                              Cont consistencyRead O namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle namedRead pkg)
                                    hsame ∧
                                  UnaryHistory sourceRoute ∧
                                    UnaryHistory endpointRead ∧
                                      UnaryHistory dischargeRead ∧
                                        UnaryHistory consistencyRead ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro sUnary qUnary eUnary dUnary kUnary oUnary nUnary sourceRouteCont
    endpointRoute dischargeRoute consistencyRoute nameRoute provenancePkg namedPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed sUnary qUnary sourceRouteCont
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed sourceUnary eUnary endpointRoute
  have dischargeUnary : UnaryHistory dischargeRead :=
    unary_cont_closed endpointUnary dUnary dischargeRoute
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed dischargeUnary kUnary consistencyRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed consistencyUnary oUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Q ∨ hsame row E ∨ hsame row D ∨ hsame row K ∨
              hsame row O ∨ hsame row sourceRoute ∨ hsame row endpointRead ∨
                hsame row dischargeRead ∨ hsame row consistencyRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Q sourceRoute ∧ Cont sourceRoute E endpointRead ∧
              Cont endpointRead D dischargeRead ∧ Cont dischargeRead K consistencyRead ∧
                Cont consistencyRead O namedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨namedRead, hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRouteCont, endpointRoute, dischargeRoute, consistencyRoute,
          nameRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, sourceUnary, endpointUnary, dischargeUnary, consistencyUnary, namedUnary⟩

end BEDC.Derived.ClosedConsistencyReductionBoundaryUp
