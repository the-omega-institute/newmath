import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp.PeanoDependencyRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusPeanoDependencyRoute [AskSetup] [PackageSetup]
    {real continuous peano initial derivative localFlow odeConsumer transport replay provenance
      localName continuousRead peanoRead initialRead odeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory real →
      UnaryHistory continuous →
        UnaryHistory peano →
          UnaryHistory initial →
            UnaryHistory odeConsumer →
              UnaryHistory localName →
                Cont real continuous continuousRead →
                  Cont continuous peano peanoRead →
                    Cont peano initial initialRead →
                      Cont initial odeConsumer odeRead →
                        Cont odeRead localName namedRead →
                          hsame transport (append provenance replay) →
                            PkgSig bundle provenance pkg →
                              PkgSig bundle localName pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row real ∨ hsame row continuous ∨ hsame row peano ∨
                                        hsame row initial ∨ hsame row odeConsumer ∨
                                          hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont real continuous continuousRead ∧
                                          Cont continuous peano peanoRead ∧
                                            Cont peano initial initialRead ∧
                                              Cont initial odeConsumer odeRead ∧
                                                Cont odeRead localName namedRead ∧
                                                  hsame transport (append provenance replay) ∧
                                                    PkgSig bundle provenance pkg ∧
                                                      PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory continuousRead ∧ UnaryHistory peanoRead ∧
                                    UnaryHistory initialRead ∧ UnaryHistory odeRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont append PkgSig hsame SemanticNameCert UnaryHistory
  intro realUnary continuousUnary peanoUnary initialUnary odeConsumerUnary localNameUnary
    continuousRoute peanoRoute initialRoute odeRoute namedRoute transportReplay provenancePkg
    localNamePkg
  have continuousReadUnary : UnaryHistory continuousRead :=
    unary_cont_closed realUnary continuousUnary continuousRoute
  have peanoReadUnary : UnaryHistory peanoRead :=
    unary_cont_closed continuousUnary peanoUnary peanoRoute
  have initialReadUnary : UnaryHistory initialRead :=
    unary_cont_closed peanoUnary initialUnary initialRoute
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed initialUnary odeConsumerUnary odeRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed odeReadUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row continuous ∨ hsame row peano ∨ hsame row initial ∨
              hsame row odeConsumer ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real continuous continuousRead ∧
              Cont continuous peano peanoRead ∧ Cont peano initial initialRead ∧
                Cont initial odeConsumer odeRead ∧ Cont odeRead localName namedRead ∧
                  hsame transport (append provenance replay) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact
        ⟨source.right, continuousRoute, peanoRoute, initialRoute, odeRoute, namedRoute,
          transportReplay, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, continuousReadUnary, peanoReadUnary, initialReadUnary, odeReadUnary,
      namedReadUnary⟩

end BEDC.Derived.CalculusUp.PeanoDependencyRoute
