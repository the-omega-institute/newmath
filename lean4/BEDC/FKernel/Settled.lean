import BEDC.FKernel.Gap
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.FKernel.Settled

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Sig
open BEDC.FKernel.Package
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert

def SettledKernelCriterion [AskSetup] [PackageSetup] [DomainSetup] [NameCertSetup] : Prop :=
  ((∀ m : BMark, msame m m) ∧
    (∀ {m n : BMark}, msame m n → msame n m) ∧
    (∀ {a b c : BMark}, msame a b → msame b c → msame a c)) ∧
  ((msame BMark.b0 BMark.b1 → False) ∧ (msame BMark.b1 BMark.b0 → False)) ∧
  ((∀ h : BHist, hsame h h) ∧
    (∀ {h k : BHist}, hsame h k → hsame k h) ∧
    (∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c)) ∧
  ((∀ {h x : BHist}, hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k) ∧
    (∀ {h x : BHist}, hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k) ∧
    (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False)) ∧
  (∀ {h r r' : BHist} {m : BMark}, Ext h m r → Ext h m r' → hsame r r') ∧
  (∀ {h k r r' : BHist}, Cont h k r → Cont h k r' → hsame r r') ∧
  ((∀ k : BHist, Cont .Empty k k) ∧
    (∀ {h r : BHist}, Cont h .Empty r → hsame r h)) ∧
  (∀ {a b c ab bc : BHist},
    Cont a b ab → Cont b c bc →
      ∃ left : BHist, ∃ right : BHist,
        Cont ab c left ∧ Cont a bc right ∧ hsame left right) ∧
  (∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h s t : BHist},
    AskPolicy D → D h → SigRel bundle h s → SigRel bundle h t → hsame s t) ∧
  (∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop}, AskPolicy D →
    (∀ {h : BHist}, D h → SameSig bundle h h) ∧
      (∀ {h k : BHist}, SameSig bundle h k → SameSig bundle k h) ∧
      (∀ {h k l : BHist}, D k → SameSig bundle h k → SameSig bundle k l →
        SameSig bundle h l)) ∧
  (∀ {bundle : ProbeBundle ProbeName}, PackagePolicy bundle →
    (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) ∧
      (∀ {s t : BHist} {p q : Pkg},
        hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q) ∧
      (∀ {p q : Pkg}, psame bundle p q →
        ∃ s : BHist, ∃ t : BHist,
          TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t)) ∧
  (∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist},
    GapPolicy bundle D → InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
  (∀ {bundle : ProbeBundle ProbeName} {D : Domain},
    AskPolicy (InDom D) → PackageTokenPolicy bundle →
      (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) →
        (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
        (∀ {h k : BHist} {p q : Pkg},
          InGapSig bundle D p h → InGapSig bundle D q k →
            (psame bundle p q ↔
              ∃ s : BHist, ∃ t : BHist,
                SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t))) ∧
  (∀ {Mid Final : Type} {D : Domain}
      {firstGap : Mid → BHist → Prop} {secondGap : Final → Mid → Prop},
    (∀ {h : BHist}, InDom D h → ∃ y : Mid, firstGap y h) →
    (∀ {y : Mid},
      (∃ h : BHist, InDom D h ∧ firstGap y h) → ∃ z : Final, secondGap z y) →
    ∀ {h : BHist}, InDom D h →
      ∃ z : Final, ∃ y : Mid, firstGap y h ∧ secondGap z y) ∧
  Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.UnaryName) ∧
  Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.AddName) ∧
  (Nonempty (@StabilityCert MinimalNameCertSetup) ∧
    Nonempty (@LedgerPolicy MinimalNameCertSetup)) ∧
  (∀ {Source Target Ledger : Type}
      {sourceSame : Source → Source → Prop} {targetSame : Target → Target → Prop}
      (cert :
        { map : Source → Target //
          (∀ {a b : Source}, sourceSame a b → targetSame (map a) (map b)) ∧
            Nonempty Ledger })
      {a b : Source},
    sourceSame a b → targetSame (cert.val a) (cert.val b))

theorem settledKernelCriterion_from_current_targets [AskSetup] [PackageSetup] [DomainSetup]
    [NameCertSetup] : SettledKernelCriterion := by
  unfold SettledKernelCriterion
  constructor
  · exact msame_equivalence
  · constructor
    · exact msame_no_confusion
    · constructor
      · exact hsame_equivalence
      · constructor
        · exact hsame_constructor_inversion_full
        · constructor
          · exact ext_deterministic
          · constructor
            · exact cont_deterministic
            · constructor
              · exact cont_unit_laws
              · constructor
                · intro a b c ab bc hab hbc
                  exact cont_assoc_exists_hsame hab hbc
                · constructor
                  · exact sig_deterministic
                  · constructor
                    · intro bundle D policy
                      exact sameSig_equivalence (bundle := bundle) (D := D) policy
                    · constructor
                      · intro bundle policy
                        exact packagePolicy_field_witnesses policy
                      · constructor
                        · exact gap_coverage
                        · constructor
                          · intro bundle D askPolicy packagePolicy tokenExists
                            exact exact_globalize_classifies_signatures
                              (bundle := bundle) (D := D) askPolicy packagePolicy tokenExists
                          · constructor
                            · intro Mid Final D firstGap secondGap firstCoverage secondCoverage h hIn
                              exact composite_coverage
                                (Mid := Mid) (Final := Final) (D := D)
                                (firstGap := firstGap) (secondGap := secondGap)
                                firstCoverage secondCoverage hIn
                            · constructor
                              · exact BEDC.FKernel.Unary.nat_up_name_certificate_exists
                              · constructor
                                · exact BEDC.FKernel.Unary.add_up_name_certificate_exists
                                · constructor
                                  · exact BEDC.FKernel.Unary.add_up_certificate_stability_and_ledger
                                  · intro Source Target Ledger sourceSame targetSame cert a b same
                                    exact function_like_interfaces_require_descent cert same

theorem settledKernelCriterion_globalize_exactness_projection [AskSetup] [PackageSetup]
    [DomainSetup] [NameCertSetup] :
    SettledKernelCriterion →
      ∀ {bundle : ProbeBundle ProbeName} {D : Domain},
        AskPolicy (InDom D) →
          PackageTokenPolicy bundle →
            (∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p) →
              (∀ {h : BHist}, InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
                (∀ {h k : BHist} {p q : Pkg},
                  InGapSig bundle D p h →
                    InGapSig bundle D q k →
                      (psame bundle p q ↔
                        ∃ s : BHist, ∃ t : BHist,
                          SigRel bundle h s ∧ SigRel bundle k t ∧ hsame s t)) := by
  intro criterion bundle D askPolicy packagePolicy tokenExists
  cases criterion with
  | intro _ rest =>
      cases rest with
      | intro _ rest =>
          cases rest with
          | intro _ rest =>
              cases rest with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro _ rest =>
                          cases rest with
                          | intro _ rest =>
                              cases rest with
                              | intro _ rest =>
                                  cases rest with
                                  | intro _ rest =>
                                      cases rest with
                                      | intro _ rest =>
                                          cases rest with
                                          | intro _ rest =>
                                              cases rest with
                                              | intro _ rest =>
                                                  cases rest with
                                                  | intro globalizeExactness _ =>
                                                      exact globalizeExactness
                                                        askPolicy packagePolicy tokenExists

theorem settledKernelCriterion_signature_kernel_projection [AskSetup] [PackageSetup]
    [DomainSetup] [NameCertSetup] :
    SettledKernelCriterion →
      (∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop} {h s t : BHist},
        AskPolicy D → D h → SigRel bundle h s → SigRel bundle h t → hsame s t) ∧
      (∀ {bundle : ProbeBundle ProbeName} {D : BHist → Prop}, AskPolicy D →
        (∀ {h : BHist}, D h → SameSig bundle h h) ∧
          (∀ {h k : BHist}, SameSig bundle h k → SameSig bundle k h) ∧
          (∀ {h k l : BHist}, D k → SameSig bundle h k → SameSig bundle k l →
            SameSig bundle h l)) := by
  intro criterion
  cases criterion with
  | intro _ rest =>
      cases rest with
      | intro _ rest =>
          cases rest with
          | intro _ rest =>
              cases rest with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro _ rest =>
                          cases rest with
                          | intro _ rest =>
                              cases rest with
                              | intro _ rest =>
                                  cases rest with
                                  | intro signatureDeterminacy rest =>
                                      cases rest with
                                      | intro sameSigEquivalence _ =>
                                          exact ⟨signatureDeterminacy, sameSigEquivalence⟩

theorem settledKernelCriterion_namecert_projection [AskSetup] [PackageSetup]
    [DomainSetup] [NameCertSetup] :
    SettledKernelCriterion →
      Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.UnaryName) ∧
      Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.AddName) ∧
      (Nonempty (@StabilityCert MinimalNameCertSetup) ∧
        Nonempty (@LedgerPolicy MinimalNameCertSetup)) := by
  intro criterion
  cases criterion with
  | intro _ rest =>
      cases rest with
      | intro _ rest =>
          cases rest with
          | intro _ rest =>
              cases rest with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro _ rest =>
                          cases rest with
                          | intro _ rest =>
                              cases rest with
                              | intro _ rest =>
                                  cases rest with
                                  | intro _ rest =>
                                      cases rest with
                                      | intro _ rest =>
                                          cases rest with
                                          | intro _ rest =>
                                              cases rest with
                                              | intro _ rest =>
                                                  cases rest with
                                                  | intro _ rest =>
                                                      cases rest with
                                                      | intro _ rest =>
                                                          cases rest with
                                                          | intro unaryName rest =>
                                                              cases rest with
                                                              | intro addName rest =>
                                                                  cases rest with
                                                                  | intro stabilityAndLedger _ =>
                                                                      exact
                                                                        ⟨unaryName,
                                                                          addName,
                                                                          stabilityAndLedger⟩

theorem layer_isolation_policy_memory_projection [AskSetup] [PackageSetup] [DomainSetup]
    [NameCertSetup] :
    SettledKernelCriterion →
      (∀ {bundle : ProbeBundle ProbeName} {D : Domain} {h : BHist},
        GapPolicy bundle D → InDom D h → ∃ p : Pkg, InGapSig bundle D p h) ∧
      Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.UnaryName) ∧
      Nonempty (@NameCert MinimalNameCertSetup BEDC.FKernel.Unary.AddName) := by
  intro criterion
  constructor
  · intro bundle D h policy hIn
    exact gap_coverage policy hIn
  · cases settledKernelCriterion_namecert_projection criterion with
    | intro unaryName rest =>
        cases rest with
        | intro addName _ =>
            exact And.intro unaryName addName

theorem settledKernelCriterion_history_kernel_projection [AskSetup] [PackageSetup]
    [DomainSetup] [NameCertSetup] :
    SettledKernelCriterion →
      ((∀ m : BMark, msame m m) ∧
        (∀ {m n : BMark}, msame m n → msame n m) ∧
        (∀ {a b c : BMark}, msame a b → msame b c → msame a c)) ∧
      ((msame BMark.b0 BMark.b1 → False) ∧ (msame BMark.b1 BMark.b0 → False)) ∧
      ((∀ h : BHist, hsame h h) ∧
        (∀ {h k : BHist}, hsame h k → hsame k h) ∧
        (∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c)) ∧
      ((∀ {h x : BHist}, hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k) ∧
        (∀ {h x : BHist}, hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k) ∧
        (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False)) := by
  intro criterion
  cases criterion with
  | intro markEquivalence rest =>
      cases rest with
      | intro markNoConfusion rest =>
          cases rest with
          | intro histEquivalence rest =>
              cases rest with
              | intro histInversion rest =>
                  constructor
                  · exact markEquivalence
                  · constructor
                    · exact markNoConfusion
                    · constructor
                      · exact histEquivalence
                      · exact histInversion

end BEDC.FKernel.Settled
