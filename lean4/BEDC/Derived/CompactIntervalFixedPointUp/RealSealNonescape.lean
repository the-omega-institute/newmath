import BEDC.Derived.CompactIntervalFixedPointUp.TasteGate
import BEDC.Derived.CompactIntervalFixedPointUp.WindowRegularity
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactIntervalFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointRealSealNonescape [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory N →
                    Cont J G mapRead →
                      Cont mapRead R returnRead →
                        Cont returnRead B bisectionRead →
                          Cont bisectionRead W windowRead →
                            Cont windowRead Q readbackRead →
                              Cont readbackRead E sealRead →
                                Cont sealRead N namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row J ∨ hsame row G ∨ hsame row R ∨
                                              hsame row B ∨ hsame row W ∨
                                                hsame row Q ∨ hsame row E ∨
                                                  hsame row N ∨ hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont J G mapRead ∧
                                              Cont mapRead R returnRead ∧
                                                Cont returnRead B bisectionRead ∧
                                                  Cont bisectionRead W windowRead ∧
                                                    Cont windowRead Q readbackRead ∧
                                                      Cont readbackRead E sealRead ∧
                                                        Cont sealRead N namedRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory mapRead ∧ UnaryHistory returnRead ∧
                                          UnaryHistory bisectionRead ∧
                                            UnaryHistory windowRead ∧
                                              UnaryHistory readbackRead ∧
                                                UnaryHistory sealRead ∧
                                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary nUnary mapRoute returnRoute
    bisectionRoute windowRoute readbackRoute sealRoute namedRoute packageRead namePackage
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapRoute
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J G mapRead ∧ Cont mapRead R returnRead ∧
              Cont returnRead B bisectionRead ∧ Cont bisectionRead W windowRead ∧
                Cont windowRead Q readbackRead ∧ Cont readbackRead E sealRead ∧
                  Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, mapRoute, returnRoute, bisectionRoute, windowRoute,
          readbackRoute, sealRoute, namedRoute, packageRead, namePackage⟩
  }
  exact
    ⟨cert, mapUnary, returnUnary, bisectionUnary, windowUnary, readbackUnary,
      sealUnary, namedUnary⟩

namespace RealSealNonescape

theorem CompactIntervalFixedPoint_real_seal_nonescape [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead replayRead : BHist} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory H →
                    UnaryHistory C →
                      Cont J G mapRead →
                        Cont mapRead R returnRead →
                          Cont returnRead B bisectionRead →
                            Cont bisectionRead W windowRead →
                              Cont windowRead Q readbackRead →
                                Cont readbackRead E sealRead →
                                  Cont H C replayRead →
                                    hsame sealRead
                                        (append (append (append (append (append (append J G) R) B) W) Q) E) ∧
                                      UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont append hsame UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary hUnary cUnary mapCont
    returnCont bisectionCont windowCont readbackCont sealCont replayCont
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapCont
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnCont
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayCont
  have mapExact : hsame mapRead (append J G) :=
    mapCont
  have returnExact : hsame returnRead (append (append J G) R) :=
    returnCont.trans (congrArg (fun row => append row R) mapExact)
  have bisectionExact : hsame bisectionRead (append (append (append J G) R) B) :=
    bisectionCont.trans (congrArg (fun row => append row B) returnExact)
  have windowExact : hsame windowRead (append (append (append (append J G) R) B) W) :=
    windowCont.trans (congrArg (fun row => append row W) bisectionExact)
  have readbackExact : hsame readbackRead
      (append (append (append (append (append J G) R) B) W) Q) :=
    readbackCont.trans (congrArg (fun row => append row Q) windowExact)
  have sealExact : hsame sealRead
      (append (append (append (append (append (append J G) R) B) W) Q) E) :=
    sealCont.trans (congrArg (fun row => append row E) readbackExact)
  exact ⟨sealExact, sealUnary, replayUnary⟩

end RealSealNonescape

end BEDC.Derived.CompactIntervalFixedPointUp
