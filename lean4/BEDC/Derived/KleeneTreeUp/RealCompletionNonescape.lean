import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeRealCompletionNonescape [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      prefixRead nodeRead obstructionRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg →
      Cont stream listSpine prefixRead →
        Cont prefixRead boolLedger nodeRead →
          Cont nodeRead obstruction obstructionRead →
            Cont obstructionRead provenance realSeal →
              PkgSig bundle realSeal pkg →
                UnaryHistory stream ∧ UnaryHistory obstructionRead ∧ UnaryHistory realSeal ∧
                  Cont stream listSpine prefixRead ∧ Cont prefixRead boolLedger nodeRead ∧
                    Cont nodeRead obstruction obstructionRead ∧
                      Cont obstructionRead provenance realSeal ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier streamPrefix prefixNode nodeObstruction obstructionRealSeal realSealPkg
  obtain ⟨_treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, provenanceUnary, _localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed streamUnary listUnary streamPrefix
  have nodeUnary : UnaryHistory nodeRead :=
    unary_cont_closed prefixUnary boolUnary prefixNode
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed nodeUnary obstructionUnary nodeObstruction
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed obstructionReadUnary provenanceUnary obstructionRealSeal
  exact
    ⟨streamUnary, obstructionReadUnary, realSealUnary, streamPrefix, prefixNode,
      nodeObstruction, obstructionRealSeal, provenancePkg, realSealPkg⟩

end BEDC.Derived.KleeneTreeUp
