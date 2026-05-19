import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DependentCodomainClosurePreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DependentCodomainClosurePreservationPacket [AskSetup] [PackageSetup]
    (pi domain arg reduced codomainSource codomainTarget betaClosed substClosed boundary
      transport ledger htrans replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory pi ∧ UnaryHistory domain ∧ UnaryHistory arg ∧ UnaryHistory reduced ∧
    UnaryHistory codomainSource ∧ UnaryHistory codomainTarget ∧ UnaryHistory betaClosed ∧
      UnaryHistory substClosed ∧ UnaryHistory boundary ∧ UnaryHistory transport ∧
        UnaryHistory ledger ∧ UnaryHistory htrans ∧ UnaryHistory replay ∧
          UnaryHistory provenance ∧ UnaryHistory name ∧ Cont pi domain arg ∧
            Cont arg reduced codomainSource ∧
              Cont codomainSource codomainTarget transport ∧
                Cont betaClosed substClosed ledger ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg

theorem DependentCodomainClosurePreservationObligations [AskSetup] [PackageSetup]
    {pi domain arg reduced codomainSource codomainTarget betaClosed substClosed boundary
      transport ledger htrans replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DependentCodomainClosurePreservationPacket pi domain arg reduced codomainSource
        codomainTarget betaClosed substClosed boundary transport ledger htrans replay provenance
        name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          DependentCodomainClosurePreservationPacket pi domain arg reduced codomainSource
              codomainTarget betaClosed substClosed boundary transport ledger htrans replay
              provenance name bundle pkg ∧
            (hsame row pi ∨ hsame row domain ∨ hsame row arg ∨ hsame row reduced ∨
              hsame row codomainSource ∨ hsame row codomainTarget ∨
                hsame row betaClosed ∨ hsame row substClosed ∨ hsame row transport ∨
                  hsame row ledger))
        (fun _row : BHist =>
          Cont pi domain arg ∧ Cont arg reduced codomainSource ∧
            Cont codomainSource codomainTarget transport ∧ PkgSig bundle provenance pkg)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨piUnary, domainUnary, argUnary, reducedUnary, codomainSourceUnary,
    codomainTargetUnary, betaClosedUnary, substClosedUnary, _boundaryUnary, transportUnary,
    ledgerUnary, _htransUnary, _replayUnary, _provenanceUnary, _nameUnary, piDomainArg,
    argReducedCodomainSource, codomainSourceTargetTransport, _betaSubstLedger, namePkg,
    provenancePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro pi ⟨packetWitness, Or.inl (hsame_refl pi)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl samePi =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) samePi)
          | inr rest =>
              cases rest with
              | inl sameDomain =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDomain))
              | inr rest =>
                  cases rest with
                  | inl sameArg =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameArg)))
                  | inr rest =>
                      cases rest with
                      | inl sameReduced =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameReduced))))
                      | inr rest =>
                          cases rest with
                          | inl sameCodomainSource =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameCodomainSource)))))
                          | inr rest =>
                              cases rest with
                              | inl sameCodomainTarget =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameCodomainTarget))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameBetaClosed =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameBetaClosed)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameSubstClosed =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans (hsame_symm sameRows)
                                                            sameSubstClosed))))))))
                                      | inr rest =>
                                          cases rest with
                                          | inl sameTransport =>
                                              exact Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameTransport)))))))))
                                          | inr sameLedger =>
                                              exact Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameLedger)))))))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨piDomainArg, argReducedCodomainSource, codomainSourceTargetTransport,
          provenancePkg⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl samePi =>
            exact unary_transport piUnary (hsame_symm samePi)
        | inr rest =>
            cases rest with
            | inl sameDomain =>
                exact unary_transport domainUnary (hsame_symm sameDomain)
            | inr rest =>
                cases rest with
                | inl sameArg =>
                    exact unary_transport argUnary (hsame_symm sameArg)
                | inr rest =>
                    cases rest with
                    | inl sameReduced =>
                        exact unary_transport reducedUnary (hsame_symm sameReduced)
                    | inr rest =>
                        cases rest with
                        | inl sameCodomainSource =>
                            exact
                              unary_transport codomainSourceUnary
                                (hsame_symm sameCodomainSource)
                        | inr rest =>
                            cases rest with
                            | inl sameCodomainTarget =>
                                exact
                                  unary_transport codomainTargetUnary
                                    (hsame_symm sameCodomainTarget)
                            | inr rest =>
                                cases rest with
                                | inl sameBetaClosed =>
                                    exact
                                      unary_transport betaClosedUnary
                                        (hsame_symm sameBetaClosed)
                                | inr rest =>
                                    cases rest with
                                    | inl sameSubstClosed =>
                                        exact
                                          unary_transport substClosedUnary
                                            (hsame_symm sameSubstClosed)
                                    | inr rest =>
                                        cases rest with
                                        | inl sameTransport =>
                                            exact
                                              unary_transport transportUnary
                                                (hsame_symm sameTransport)
                                        | inr sameLedger =>
                                            exact unary_transport ledgerUnary
                                              (hsame_symm sameLedger)
      exact ⟨rowUnary, namePkg, provenancePkg⟩
  }

end BEDC.Derived.DependentCodomainClosurePreservationUp
