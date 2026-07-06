import BEDC.Derived.CauchyRealFieldUp.ReciprocalBoundary

namespace BEDC.Derived.CauchyRealFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRealFieldCarrier_scoped_operation_route [AskSetup] [PackageSetup]
    {regseq stream dyadic realSeal add product reciprocal order transport replay provenance
      localName addRead mulRead orderGate reciprocalRead fieldRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealFieldCarrier regseq stream dyadic realSeal add product reciprocal order transport
        replay provenance localName bundle pkg →
      Cont regseq stream addRead →
        Cont addRead dyadic mulRead →
          Cont order reciprocal orderGate →
            Cont orderGate dyadic reciprocalRead →
              Cont replay realSeal fieldRead →
                Cont fieldRead localName scopedRead →
                  PkgSig bundle scopedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
                            hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                              hsame row reciprocal ∨ hsame row order ∨ hsame row scopedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont regseq stream addRead ∧
                            Cont addRead dyadic mulRead ∧
                              Cont order reciprocal orderGate ∧
                                Cont orderGate dyadic reciprocalRead ∧
                                  Cont replay realSeal fieldRead ∧
                                    Cont fieldRead localName scopedRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle scopedRead pkg)
                        hsame ∧ UnaryHistory addRead ∧ UnaryHistory mulRead ∧
                      UnaryHistory orderGate ∧ UnaryHistory reciprocalRead ∧
                        UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier addRoute mulRoute orderRoute reciprocalRoute fieldRoute scopedRoute scopedPkg
  have regseqUnary : UnaryHistory regseq := carrier.left
  have streamUnary : UnaryHistory stream := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have realSealUnary : UnaryHistory realSeal := carrier.right.right.right.left
  have reciprocalUnary : UnaryHistory reciprocal :=
    carrier.right.right.right.right.right.right.left
  have orderUnary : UnaryHistory order :=
    carrier.right.right.right.right.right.right.right.left
  have replayUnary : UnaryHistory replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have localNameUnary : UnaryHistory localName :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have addReadUnary : UnaryHistory addRead :=
    unary_cont_closed regseqUnary streamUnary addRoute
  have mulReadUnary : UnaryHistory mulRead :=
    unary_cont_closed addReadUnary dyadicUnary mulRoute
  have orderGateUnary : UnaryHistory orderGate :=
    unary_cont_closed orderUnary reciprocalUnary orderRoute
  have reciprocalReadUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed orderGateUnary dyadicUnary reciprocalRoute
  have fieldReadUnary : UnaryHistory fieldRead :=
    unary_cont_closed replayUnary realSealUnary fieldRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed fieldReadUnary localNameUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regseq ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row realSeal ∨ hsame row add ∨ hsame row product ∨
                hsame row reciprocal ∨ hsame row order ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regseq stream addRead ∧
              Cont addRead dyadic mulRead ∧ Cont order reciprocal orderGate ∧
                Cont orderGate dyadic reciprocalRead ∧ Cont replay realSeal fieldRead ∧
                  Cont fieldRead localName scopedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨scopedRead, ⟨hsame_refl scopedRead, scopedReadUnary⟩⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, addRoute, mulRoute, orderRoute, reciprocalRoute, fieldRoute,
          scopedRoute, provenancePkg, scopedPkg⟩
  }
  exact
    ⟨cert, addReadUnary, mulReadUnary, orderGateUnary, reciprocalReadUnary,
      scopedReadUnary⟩

end BEDC.Derived.CauchyRealFieldUp
