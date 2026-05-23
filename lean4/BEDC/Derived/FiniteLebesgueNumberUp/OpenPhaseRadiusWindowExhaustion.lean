import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRegSeqStreamNameNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow regseqRead realRead
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window transport regseqRead →
        Cont regseqRead route realRead →
          PkgSig bundle realRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row window ∨ hsame row regseqRead ∨ hsame row realRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧
                    hsame row realRead)
                hsame ∧
              UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory regseqRead ∧
                UnaryHistory realRead ∧ Cont window transport regseqRead ∧
                  Cont regseqRead route realRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realRead pkg ∧
                      (Cont realRead (BHist.e0 hostTail) regseqRead → False) ∧
                        (Cont realRead (BHist.e1 hostTail) regseqRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowTransportRegseq regseqRouteReal realPkg
  obtain ⟨_coverUnary, windowUnary, _radiusUnary, _meshUnary, transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary transportUnary windowTransportRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary routeUnary regseqRouteReal
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row window ∨ hsame row regseqRead ∨ hsame row realRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg ∧
            hsame row realRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead sourceReal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, realPkg, source.left⟩
    }
  exact
    ⟨cert, windowUnary, transportUnary, regseqUnary, realUnary, windowTransportRegseq,
      regseqRouteReal, provenancePkg, realPkg,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left regseqRouteReal hostReturn,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right regseqRouteReal hostReturn⟩

theorem FiniteLebesgueNumberRealSourceLedgerCoverage [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius streamRead →
        Cont streamRead mesh regularRead →
          Cont regularRead nameRow realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory streamRead ∧ UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                Cont window radius streamRead ∧ Cont streamRead mesh regularRead ∧
                  Cont regularRead nameRow realRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowRadiusStream streamMeshRegular regularNameReal realPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary meshUnary streamMeshRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  exact
    ⟨streamUnary, regularUnary, realUnary, windowRadiusStream, streamMeshRegular,
      regularNameReal, provenancePkg, realPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
