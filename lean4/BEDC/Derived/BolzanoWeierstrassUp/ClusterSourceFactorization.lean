import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cluster_source_factorization [AskSetup] [PackageSetup]
    {S K R Q E H C P N boundedSource intervalTree subsequenceRow regseqRead clusterSeal
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S H boundedSource ->
        Cont boundedSource K intervalTree ->
          Cont intervalTree R subsequenceRow ->
            Cont subsequenceRow Q regseqRead ->
              Cont regseqRead E clusterSeal ->
                Cont clusterSeal C publicRead ->
                  PkgSig bundle publicRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                            hsame row E ∨ hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S H boundedSource ∧
                            Cont boundedSource K intervalTree ∧
                              Cont intervalTree R subsequenceRow ∧
                                Cont subsequenceRow Q regseqRead ∧
                                  Cont regseqRead E clusterSeal ∧
                                    Cont clusterSeal C publicRead ∧
                                      PkgSig bundle P pkg ∧
                                        PkgSig bundle publicRead pkg)
                        hsame ∧
                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundedRoute intervalRoute subsequenceRoute regseqRoute clusterRoute
    publicRoute publicPkg
  obtain ⟨sUnary, kUnary, rUnary, qUnary, eUnary, hUnary, cUnary, _pUnary, _nUnary,
    _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute, carrierPkg⟩ := carrier
  have boundedUnary : UnaryHistory boundedSource :=
    unary_cont_closed sUnary hUnary boundedRoute
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed boundedUnary kUnary intervalRoute
  have subsequenceUnary : UnaryHistory subsequenceRow :=
    unary_cont_closed intervalUnary rUnary subsequenceRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed subsequenceUnary qUnary regseqRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed regseqUnary eUnary clusterRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed clusterUnary cUnary publicRoute
  constructor
  · exact {
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, boundedRoute, intervalRoute, subsequenceRoute, regseqRoute,
            clusterRoute, publicRoute, carrierPkg, publicPkg⟩
    }
  · exact publicUnary

end BEDC.Derived.BolzanoWeierstrassUp
