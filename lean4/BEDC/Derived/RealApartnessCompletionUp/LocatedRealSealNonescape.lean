import BEDC.Derived.RealApartnessCompletionUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionLocatedRealSealNonescape [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay provenance
      localName windowRead readbackRead toleranceRead sealRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory apartness →
      UnaryHistory separation →
        UnaryHistory completion →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory tolerance →
                UnaryHistory sealRow →
                  UnaryHistory transport →
                    UnaryHistory replay →
                      Cont apartness separation completion →
                        Cont completion stream windowRead →
                          Cont windowRead readback readbackRead →
                            Cont readbackRead tolerance toleranceRead →
                              Cont toleranceRead sealRow sealRead →
                                Cont transport replay structuralRead →
                                  PkgSig bundle provenance pkg →
                                    PkgSig bundle localName pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row sealRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row apartness ∨ hsame row separation ∨
                                              hsame row completion ∨ hsame row stream ∨
                                                hsame row readback ∨ hsame row tolerance ∨
                                                  hsame row sealRow ∨ hsame row sealRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont apartness separation completion ∧
                                                Cont completion stream windowRead ∧
                                                  Cont windowRead readback readbackRead ∧
                                                    Cont readbackRead tolerance toleranceRead ∧
                                                      Cont toleranceRead sealRow sealRead ∧
                                                        PkgSig bundle provenance pkg ∧
                                                          PkgSig bundle localName pkg)
                                          hsame ∧
                                        UnaryHistory windowRead ∧
                                          UnaryHistory readbackRead ∧
                                            UnaryHistory toleranceRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro apartnessUnary separationUnary completionUnary streamUnary readbackUnary toleranceUnary
    sealUnary transportUnary replayUnary completionRoute windowRoute readbackRoute toleranceRoute
    sealRoute structuralRoute provenancePkg localNamePkg
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed completionUnary streamUnary windowRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary readbackRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackReadUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
    hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation completion ∧
              Cont completion stream windowRead ∧ Cont windowRead readback readbackRead ∧
                Cont readbackRead tolerance toleranceRead ∧ Cont toleranceRead sealRow sealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, completionRoute, windowRoute, readbackRoute, toleranceRoute, sealRoute,
          provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, windowReadUnary, readbackReadUnary, toleranceReadUnary, sealReadUnary,
      structuralReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp
