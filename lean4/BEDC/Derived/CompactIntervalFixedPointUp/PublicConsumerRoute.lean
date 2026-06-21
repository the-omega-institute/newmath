import BEDC.Derived.CompactIntervalFixedPointUp.PublicSeal

namespace BEDC.Derived.CompactIntervalFixedPointUp.PublicConsumerRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointPublicConsumerRoute [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead sealRead
      namedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactIntervalFixedPointCarrier J G R B W Q E H C P N bundle pkg →
      Cont J G mapRead →
        Cont mapRead R returnRead →
          Cont returnRead B bisectionRead →
            Cont bisectionRead W windowRead →
              Cont windowRead Q readbackRead →
                Cont readbackRead E sealRead →
                  Cont sealRead N namedRead →
                    Cont H C publicRead →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                            (fun row : BHist =>
                              hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
                                hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont J G mapRead ∧
                                Cont mapRead R returnRead ∧
                                  Cont returnRead B bisectionRead ∧
                                    Cont bisectionRead W windowRead ∧
                                      Cont windowRead Q readbackRead ∧
                                        Cont readbackRead E sealRead ∧
                                          Cont sealRead N namedRead ∧
                                            Cont H C publicRead ∧ PkgSig bundle publicRead pkg)
                            hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier locatedMap mapReturn returnBisection bisectionWindow windowReadback
    readbackSeal sealName publicRoute publicPkg
  obtain ⟨jUnary, gUnary, rUnary, bUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
    _pUnary, nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have mapReadUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary locatedMap
  have returnReadUnary : UnaryHistory returnRead :=
    unary_cont_closed mapReadUnary rUnary mapReturn
  have bisectionReadUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnReadUnary bUnary returnBisection
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionReadUnary wUnary bisectionWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary qUnary windowReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary eUnary readbackSeal
  have _namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary nUnary sealName
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary cUnary publicRoute
  have sourcePublic :
      (fun row : BHist =>
        hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary, publicPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J G mapRead ∧ Cont mapRead R returnRead ∧
              Cont returnRead B bisectionRead ∧ Cont bisectionRead W windowRead ∧
                Cont windowRead Q readbackRead ∧ Cont readbackRead E sealRead ∧
                  Cont sealRead N namedRead ∧ Cont H C publicRead ∧
                    PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.left, locatedMap, mapReturn, returnBisection, bisectionWindow,
        windowReadback, readbackSeal, sealName, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicReadUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.PublicConsumerRoute
