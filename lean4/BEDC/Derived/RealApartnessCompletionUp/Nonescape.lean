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

theorem RealApartnessCompletionNonescape [AskSetup] [PackageSetup]
    {apartness separated completion stream readback tolerance sealRow transport replay
      provenance name completionRead toleranceRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory apartness →
      UnaryHistory separated →
        UnaryHistory stream →
          UnaryHistory readback →
            UnaryHistory tolerance →
              UnaryHistory sealRow →
                UnaryHistory name →
                  Cont apartness separated completionRead →
                    Cont stream readback toleranceRead →
                      Cont toleranceRead sealRow sealRead →
                        Cont sealRead name namedRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle namedRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row apartness ∨ hsame row separated ∨
                                      hsame row completionRead ∨ hsame row stream ∨
                                        hsame row readback ∨ hsame row tolerance ∨
                                          hsame row sealRow ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont apartness separated completionRead ∧
                                      Cont stream readback toleranceRead ∧
                                        Cont toleranceRead sealRow sealRead ∧
                                          Cont sealRead name namedRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle namedRead pkg)
                                  hsame ∧
                                UnaryHistory completionRead ∧ UnaryHistory toleranceRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro apartnessUnary separatedUnary streamUnary readbackUnary toleranceUnary sealUnary nameUnary
    completionRoute toleranceRoute sealRoute namedRoute provenancePkg namedPkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed apartnessUnary separatedUnary completionRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamUnary readbackUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separated ∨ hsame row completionRead ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separated completionRead ∧
              Cont stream readback toleranceRead ∧ Cont toleranceRead sealRow sealRead ∧
                Cont sealRead name namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, completionRoute, toleranceRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, completionUnary, toleranceReadUnary, sealReadUnary, namedReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp
