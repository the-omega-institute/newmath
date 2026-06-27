import BEDC.Derived.AnchorStabilityCertificateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AnchorStabilityCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem AnchorStabilityCertificateCarrier_route_exhaustion
    {F I R K L H C P N observerFamilyRead routeClassifierRead ledgerRead
      relationalRead : BHist} :
    Cont F R observerFamilyRead ->
      Cont observerFamilyRead K routeClassifierRead ->
        Cont routeClassifierRead L ledgerRead ->
          Cont ledgerRead C relationalRead ->
            UnaryHistory F ->
              UnaryHistory R ->
                UnaryHistory K ->
                  UnaryHistory L ->
                    UnaryHistory C ->
                      SemanticNameCert
                        (fun row : BHist => hsame row relationalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row I ∨ hsame row R ∨ hsame row K ∨
                            hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row relationalRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont F R observerFamilyRead ∧
                            Cont observerFamilyRead K routeClassifierRead ∧
                              Cont routeClassifierRead L ledgerRead ∧
                                Cont ledgerRead C relationalRead)
                        hsame ∧
                        UnaryHistory observerFamilyRead ∧
                          UnaryHistory routeClassifierRead ∧ UnaryHistory ledgerRead ∧
                            UnaryHistory relationalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro contFR contObserverK contRouteL contLedgerC fUnary rUnary kUnary lUnary cUnary
  have observerUnary : UnaryHistory observerFamilyRead :=
    unary_cont_closed fUnary rUnary contFR
  have routeUnary : UnaryHistory routeClassifierRead :=
    unary_cont_closed observerUnary kUnary contObserverK
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routeUnary lUnary contRouteL
  have relationalUnary : UnaryHistory relationalRead :=
    unary_cont_closed ledgerUnary cUnary contLedgerC
  constructor
  · exact
      { core := {
          carrier_inhabited :=
            Exists.intro relationalRead
              (And.intro (hsame_refl relationalRead) relationalUnary)
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row other same
            exact hsame_symm same
          equiv_trans := by
            intro row other third sameRO sameOT
            exact hsame_trans sameRO sameOT
          carrier_respects_equiv := by
            intro row other same source
            exact
              And.intro
                (hsame_trans (hsame_symm same) source.left)
                (unary_transport source.right same) }
        pattern_sound := by
          intro row source
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))
        ledger_sound := by
          intro row source
          exact
            And.intro source.right
              (And.intro contFR
                (And.intro contObserverK
                  (And.intro contRouteL contLedgerC))) }
  · exact
      And.intro observerUnary
        (And.intro routeUnary (And.intro ledgerUnary relationalUnary))

end BEDC.Derived.AnchorStabilityCertificateUp
