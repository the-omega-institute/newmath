import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeSpeckerBoundaryRoute [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance localName
      prefixRead nodeRead obstructionRead speckerRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        localName bundle pkg →
      Cont stream listSpine prefixRead →
        Cont prefixRead boolLedger nodeRead →
          Cont nodeRead obstruction obstructionRead →
            Cont obstructionRead provenance speckerRead →
              Cont speckerRead localName realSeal →
                PkgSig bundle realSeal pkg →
                  UnaryHistory stream ∧ UnaryHistory obstructionRead ∧
                    UnaryHistory speckerRead ∧ UnaryHistory realSeal ∧
                      Cont stream listSpine prefixRead ∧
                        Cont prefixRead boolLedger nodeRead ∧
                          Cont nodeRead obstruction obstructionRead ∧
                            Cont obstructionRead provenance speckerRead ∧
                              Cont speckerRead localName realSeal ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier streamPrefix prefixNode nodeObstruction obstructionSpecker speckerReal
    realSealPkg
  obtain ⟨_treeUnary, boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, provenanceUnary, localNameUnary, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed streamUnary listUnary streamPrefix
  have nodeUnary : UnaryHistory nodeRead :=
    unary_cont_closed prefixUnary boolUnary prefixNode
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed nodeUnary obstructionUnary nodeObstruction
  have speckerReadUnary : UnaryHistory speckerRead :=
    unary_cont_closed obstructionReadUnary provenanceUnary obstructionSpecker
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed speckerReadUnary localNameUnary speckerReal
  exact
    ⟨streamUnary, obstructionReadUnary, speckerReadUnary, realSealUnary, streamPrefix,
      prefixNode, nodeObstruction, obstructionSpecker, speckerReal, provenancePkg,
      realSealPkg⟩

end BEDC.Derived.KleeneTreeUp
