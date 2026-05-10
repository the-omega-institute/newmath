import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffGaloisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem DiffGaloisFaithfulActionLedger_basis_fold_surface
    {seed action actionLedger sourceSurface : BHist} {basisRows : List BHist} :
    UnaryHistory seed -> UnaryHistory action ->
      (forall row : BHist, List.Mem row basisRows -> UnaryHistory row) ->
        Cont (List.foldl append seed basisRows) action actionLedger ->
          Cont seed actionLedger sourceSurface ->
            UnaryHistory (List.foldl append seed basisRows) ∧ UnaryHistory actionLedger ∧
              UnaryHistory sourceSurface ∧
                hsame actionLedger (append (List.foldl append seed basisRows) action) ∧
                  hsame sourceSurface (append seed actionLedger) := by
  intro seedUnary actionUnary basisUnary actionRow sourceRow
  have foldUnary :
      forall {start : BHist} {rows : List BHist},
        UnaryHistory start ->
          (forall row : BHist, List.Mem row rows -> UnaryHistory row) ->
            UnaryHistory (List.foldl append start rows) := by
    intro start rows startUnary rowsUnary
    induction rows generalizing start with
    | nil =>
        exact startUnary
    | cons head tail ih =>
        have headUnary : UnaryHistory head :=
          rowsUnary head (List.Mem.head tail)
        have nextUnary : UnaryHistory (append start head) :=
          unary_append_closed startUnary headUnary
        exact ih nextUnary (by
          intro row rowMem
          exact rowsUnary row (List.Mem.tail head rowMem))
  have basisFoldUnary : UnaryHistory (List.foldl append seed basisRows) :=
    foldUnary seedUnary basisUnary
  have actionLedgerUnary : UnaryHistory actionLedger :=
    unary_cont_closed basisFoldUnary actionUnary actionRow
  have sourceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed seedUnary actionLedgerUnary sourceRow
  exact And.intro basisFoldUnary
    (And.intro actionLedgerUnary
      (And.intro sourceUnary
        (And.intro actionRow sourceRow)))

def DiffGaloisPicardVessiotPacket [AskSetup] [PackageSetup]
    (differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory differentialField ∧
    UnaryHistory operatorCoefficients ∧
      UnaryHistory seqBasis ∧
        UnaryHistory fundamentalSolution ∧
          UnaryHistory galoisAction ∧
            UnaryHistory constantField ∧
              Cont seqBasis fundamentalSolution solutionLedger ∧
                Cont differentialField operatorCoefficients actionLedger ∧
                  Cont solutionLedger actionLedger endpoint ∧
                    SigRel bundle endpoint provenance ∧
                      PkgSig bundle provenance pkg

theorem DiffGaloisPicardVessiotPacket_solution_space_obligation [AskSetup] [PackageSetup]
    {differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiffGaloisPicardVessiotPacket differentialField operatorCoefficients seqBasis
      fundamentalSolution galoisAction constantField solutionLedger actionLedger endpoint
      provenance bundle pkg ->
        UnaryHistory solutionLedger ∧
          UnaryHistory actionLedger ∧
            UnaryHistory endpoint ∧
              hsame solutionLedger (append seqBasis fundamentalSolution) ∧
                hsame actionLedger (append differentialField operatorCoefficients) ∧
                  hsame endpoint (append solutionLedger actionLedger) ∧
                    SigRel bundle endpoint provenance ∧
                      PkgSig bundle provenance pkg := by
  intro packet
  have solutionUnary : UnaryHistory solutionLedger :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.left
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed solutionUnary actionUnary
      packet.right.right.right.right.right.right.right.right.left
  exact And.intro solutionUnary
    (And.intro actionUnary
      (And.intro endpointUnary
        (And.intro packet.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.right.left
                  packet.right.right.right.right.right.right.right.right.right.right))))))

theorem DiffGaloisPicardVessiotPacket_faithful_action_obligation [AskSetup] [PackageSetup]
    {differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance faithfulActionLedger
      fixedFieldLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiffGaloisPicardVessiotPacket differentialField operatorCoefficients seqBasis
      fundamentalSolution galoisAction constantField solutionLedger actionLedger endpoint
      provenance bundle pkg ->
        Cont galoisAction seqBasis faithfulActionLedger ->
          Cont faithfulActionLedger constantField fixedFieldLedger ->
            UnaryHistory faithfulActionLedger ∧ UnaryHistory fixedFieldLedger ∧
              hsame faithfulActionLedger (append galoisAction seqBasis) ∧
                hsame fixedFieldLedger (append faithfulActionLedger constantField) ∧
                  SigRel bundle endpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro packet faithfulActionRow fixedFieldRow
  have faithfulActionUnary : UnaryHistory faithfulActionLedger :=
    unary_cont_closed packet.right.right.right.right.left packet.right.right.left
      faithfulActionRow
  have fixedFieldUnary : UnaryHistory fixedFieldLedger :=
    unary_cont_closed faithfulActionUnary packet.right.right.right.right.right.left fixedFieldRow
  exact
    ⟨faithfulActionUnary, fixedFieldUnary, faithfulActionRow, fixedFieldRow,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right⟩

theorem DiffGaloisPublicCertificate_export [AskSetup] [PackageSetup]
    {differentialField operatorCoefficients seqBasis fundamentalSolution galoisAction
      constantField solutionLedger actionLedger endpoint provenance faithfulActionLedger
      fixedFieldLedger publicBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiffGaloisPicardVessiotPacket differentialField operatorCoefficients seqBasis
      fundamentalSolution galoisAction constantField solutionLedger actionLedger endpoint
      provenance bundle pkg ->
        Cont galoisAction seqBasis faithfulActionLedger ->
          Cont faithfulActionLedger constantField fixedFieldLedger ->
            Cont endpoint fixedFieldLedger publicBoundary ->
              UnaryHistory publicBoundary ∧ hsame publicBoundary (append endpoint fixedFieldLedger) ∧
                SigRel bundle endpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro packet faithfulActionRow fixedFieldRow publicBoundaryRow
  have solutionRows :=
    DiffGaloisPicardVessiotPacket_solution_space_obligation packet
  have faithfulRows :=
    DiffGaloisPicardVessiotPacket_faithful_action_obligation packet faithfulActionRow
      fixedFieldRow
  have publicBoundaryUnary : UnaryHistory publicBoundary :=
    unary_cont_closed solutionRows.right.right.left faithfulRows.right.left publicBoundaryRow
  exact
    ⟨publicBoundaryUnary, publicBoundaryRow,
      faithfulRows.right.right.right.right.left, faithfulRows.right.right.right.right.right⟩

end BEDC.Derived.DiffGaloisUp
