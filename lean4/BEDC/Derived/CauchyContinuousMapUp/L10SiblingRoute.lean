import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousMap_l10_sibling_route [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead toleranceRead sealRead clientRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.toleranceLedger toleranceRead →
          Cont toleranceRead M.realSealHandoff sealRead →
            Cont sealRead M.replay clientRead →
              Cont clientRead M.localName namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.replay ∨ hsame row M.localName ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.toleranceLedger toleranceRead ∧
                            Cont toleranceRead M.realSealHandoff sealRead ∧
                              Cont sealRead M.replay clientRead ∧
                                Cont clientRead M.localName namedRead ∧
                                  PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory imageRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory clientRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet imageRoute toleranceRoute sealRoute clientRoute nameRoute namedPkg
  obtain ⟨windowsUnary, imageReadbackUnary, toleranceLedgerUnary, realSealUnary,
    _transportUnary, replayUnary, _provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed imageUnary toleranceLedgerUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary realSealUnary sealRoute
  have clientUnary : UnaryHistory clientRead :=
    unary_cont_closed sealUnary replayUnary clientRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed clientUnary localNameUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.localName ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.toleranceLedger toleranceRead ∧
                Cont toleranceRead M.realSealHandoff sealRead ∧
                  Cont sealRead M.replay clientRead ∧
                    Cont clientRead M.localName namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, toleranceRoute, sealRoute, clientRoute, nameRoute,
          namedPkg⟩
  }
  exact
    ⟨cert, imageUnary, toleranceUnary, sealUnary, clientUnary, namedUnary⟩

end BEDC.Derived.CauchyContinuousMapUp
