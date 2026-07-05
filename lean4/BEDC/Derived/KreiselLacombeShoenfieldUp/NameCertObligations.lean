import BEDC.Derived.KreiselLacombeShoenfieldUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KreiselLacombeShoenfieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KreiselLacombeShoenfieldCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B O S R E M L H C P N observationRead windowRead readbackRead modulusRead ledgerRead
      realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory O ->
        UnaryHistory S ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory M ->
                UnaryHistory L ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory N ->
                          Cont B O observationRead ->
                            Cont observationRead M modulusRead ->
                              Cont modulusRead S windowRead ->
                                Cont windowRead R readbackRead ->
                                  Cont readbackRead L ledgerRead ->
                                    Cont ledgerRead E realRead ->
                                      Cont realRead P namedRead ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row namedRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row B ∨ hsame row O ∨
                                                  hsame row S ∨ hsame row R ∨
                                                    hsame row E ∨ hsame row M ∨
                                                      hsame row L ∨ hsame row H ∨
                                                        hsame row C ∨ hsame row P ∨
                                                          hsame row N ∨
                                                            hsame row observationRead ∨
                                                              hsame row windowRead ∨
                                                                hsame row readbackRead ∨
                                                                  hsame row modulusRead ∨
                                                                    hsame row ledgerRead ∨
                                                                      hsame row realRead ∨
                                                                        hsame row namedRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  Cont B O observationRead ∧
                                                    Cont observationRead M modulusRead ∧
                                                      Cont modulusRead S windowRead ∧
                                                        Cont windowRead R readbackRead ∧
                                                          Cont readbackRead L ledgerRead ∧
                                                            Cont ledgerRead E realRead ∧
                                                              Cont realRead P namedRead ∧
                                                                PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory observationRead ∧
                                              UnaryHistory modulusRead ∧
                                                UnaryHistory windowRead ∧
                                                  UnaryHistory readbackRead ∧
                                                    UnaryHistory ledgerRead ∧
                                                      UnaryHistory realRead ∧
                                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: KreiselLacombeShoenfieldUp BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro bUnary oUnary sUnary rUnary eUnary mUnary lUnary _hUnary _cUnary pUnary _nUnary
    observationRoute modulusRoute windowRoute readbackRoute ledgerRoute realRoute namedRoute
    namePkg
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed bUnary oUnary observationRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed observationUnary mUnary modulusRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusUnary sUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed readbackUnary lUnary ledgerRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed ledgerUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary pUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row O ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row M ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row observationRead ∨ hsame row windowRead ∨
                  hsame row readbackRead ∨ hsame row modulusRead ∨ hsame row ledgerRead ∨
                    hsame row realRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B O observationRead ∧
              Cont observationRead M modulusRead ∧ Cont modulusRead S windowRead ∧
                Cont windowRead R readbackRead ∧ Cont readbackRead L ledgerRead ∧
                  Cont ledgerRead E realRead ∧ Cont realRead P namedRead ∧
                    PkgSig bundle N pkg)
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observationRoute, modulusRoute, windowRoute, readbackRoute,
          ledgerRoute, realRoute, namedRoute, namePkg⟩
  }
  exact
    ⟨cert, observationUnary, modulusUnary, windowUnary, readbackUnary, ledgerUnary, realUnary,
      namedUnary⟩

end BEDC.Derived.KreiselLacombeShoenfieldUp
