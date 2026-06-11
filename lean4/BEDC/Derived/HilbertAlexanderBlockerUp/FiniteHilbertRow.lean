import BEDC.Derived.HilbertAlexanderBlockerUp.NameCertObligations

namespace BEDC.Derived.HilbertAlexanderBlockerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HilbertAlexanderBlockerFiniteHilbertRow [AskSetup] [PackageSetup]
    {S P T B F L A R C Q N blockerRead hilbertRead alexanderRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HilbertAlexanderBlockerCarrier S P T B F L A R C Q N bundle pkg ->
      Cont B F blockerRead ->
        Cont blockerRead L hilbertRead ->
          Cont hilbertRead A alexanderRead ->
            Cont alexanderRead N named ->
              PkgSig bundle named pkg ->
                hilbertAlexanderBlockerFields
                    (HilbertAlexanderBlockerUp.mk S P T B F L A R C Q N) =
                    [S, P, T, B, F, L, A, R, C, Q, N] ∧
                  UnaryHistory blockerRead ∧ UnaryHistory hilbertRead ∧
                    UnaryHistory alexanderRead ∧ UnaryHistory named ∧
                      Cont B F blockerRead ∧ Cont blockerRead L hilbertRead ∧
                        Cont hilbertRead A alexanderRead ∧ Cont alexanderRead N named ∧
                          PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier blockerRoute hilbertRoute alexanderRoute namedRoute namedPkg
  obtain ⟨fields, _simplicialUnary, _polynomialUnary, _traceUnary, boundaryUnary,
    blockerUnaryBase, hilbertUnaryBase, alexanderUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, _namePkg⟩ := carrier
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed boundaryUnary blockerUnaryBase blockerRoute
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed blockerUnary hilbertUnaryBase hilbertRoute
  have alexanderUnary : UnaryHistory alexanderRead :=
    unary_cont_closed hilbertUnary alexanderUnaryBase alexanderRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed alexanderUnary nameUnary namedRoute
  exact
    ⟨fields, blockerUnary, hilbertUnary, alexanderUnary, namedUnary, blockerRoute,
      hilbertRoute, alexanderRoute, namedRoute, namedPkg⟩

end BEDC.Derived.HilbertAlexanderBlockerUp
