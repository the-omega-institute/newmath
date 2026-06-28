import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp.SeparatedUniformModulusCompletionRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived
open BEDC.Derived.CauchyContinuousMapUp

theorem CauchyContinuousMap_separated_uniform_modulus_completion_route
    [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead sealRead uniformRead completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay uniformRead →
            Cont uniformRead M.localName completionRead →
              Cont completionRead BHist.Empty publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.replay ∨ hsame row M.localName ∨
                              hsame row completionRead ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.replay uniformRead ∧
                              Cont uniformRead M.localName completionRead ∧
                                Cont completionRead BHist.Empty publicRead ∧
                                  PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory uniformRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute uniformRoute completionRoute publicRoute publicPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, realSealUnary,
    _transportUnary, replayUnary, _provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary realSealUnary sealRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary replayUnary uniformRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed uniformUnary localNameUnary completionRoute
  have publicUnary : UnaryHistory publicRead := by
    cases publicRoute
    exact completionUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.localName ∨
                  hsame row completionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay uniformRead ∧
                  Cont uniformRead M.localName completionRead ∧
                    Cont completionRead BHist.Empty publicRead ∧
                      PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, sealRoute, uniformRoute, completionRoute,
          publicRoute, publicPkg⟩
  }
  exact ⟨cert, uniformUnary, completionUnary, publicUnary⟩

end BEDC.Derived.CauchyContinuousMapUp.SeparatedUniformModulusCompletionRoute
