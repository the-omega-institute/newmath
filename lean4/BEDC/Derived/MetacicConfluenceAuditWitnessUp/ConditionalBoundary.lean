import BEDC.Derived.MetacicConfluenceAuditWitnessUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetacicConfluenceAuditWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetacicConfluenceAuditWitnessCarrier [AskSetup] [PackageSetup]
    (parallel substitution diamond confluence obstruction component route ledger name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory parallel ∧
    UnaryHistory substitution ∧
      UnaryHistory diamond ∧
        UnaryHistory confluence ∧
          UnaryHistory obstruction ∧
            UnaryHistory component ∧
              UnaryHistory route ∧
                UnaryHistory ledger ∧
                  UnaryHistory name ∧
                    Cont parallel substitution route ∧
                      Cont route diamond ledger ∧
                        Cont obstruction component name ∧
                          PkgSig bundle name pkg ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row name)
                              (fun row : BHist =>
                                hsame row parallel ∨ hsame row substitution ∨
                                  hsame row diamond ∨ hsame row confluence ∨
                                    hsame row name)
                              (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
                              hsame

theorem MetacicConfluenceAuditWitnessCarrier_conditional_boundary [AskSetup] [PackageSetup]
    {parallel substitution diamond confluence obstruction component route ledger name
      substRead diamondRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicConfluenceAuditWitnessCarrier parallel substitution diamond confluence
      obstruction component route ledger name bundle pkg →
      Cont parallel substitution substRead →
        Cont substRead diamond diamondRead →
          Cont diamondRead confluence confluenceRead →
            PkgSig bundle confluenceRead pkg →
              UnaryHistory parallel ∧
                UnaryHistory substitution ∧
                  UnaryHistory diamond ∧
                    UnaryHistory confluence ∧
                      UnaryHistory substRead ∧
                        UnaryHistory diamondRead ∧
                          UnaryHistory confluenceRead ∧
                            Cont parallel substitution substRead ∧
                              Cont substRead diamond diamondRead ∧
                                Cont diamondRead confluence confluenceRead ∧
                                  PkgSig bundle confluenceRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier substRoute diamondRoute confluenceRoute confluencePkg
  have parallelUnary : UnaryHistory parallel := carrier.left
  have substitutionUnary : UnaryHistory substitution := carrier.right.left
  have diamondUnary : UnaryHistory diamond := carrier.right.right.left
  have confluenceUnary : UnaryHistory confluence := carrier.right.right.right.left
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed parallelUnary substitutionUnary substRoute
  have diamondReadUnary : UnaryHistory diamondRead :=
    unary_cont_closed substReadUnary diamondUnary diamondRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed diamondReadUnary confluenceUnary confluenceRoute
  exact
    ⟨parallelUnary, substitutionUnary, diamondUnary, confluenceUnary, substReadUnary,
      diamondReadUnary, confluenceReadUnary, substRoute, diamondRoute, confluenceRoute,
      confluencePkg⟩

end BEDC.Derived.MetacicConfluenceAuditWitnessUp
