import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeierstrassApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WeierstrassApproximationCarrier [AskSetup] [PackageSetup]
    (interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory continuousMap ∧ UnaryHistory error ∧
    UnaryHistory polynomial ∧ UnaryHistory samples ∧ UnaryHistory modulus ∧
      UnaryHistory uniformError ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem WeierstrassApproximationUniformLimitConsumer [AskSetup] [PackageSetup]
    {interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName uniformLimitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassApproximationCarrier interval continuousMap error polynomial samples modulus
        uniformError transport replay provenance localName bundle pkg →
      Cont uniformError provenance uniformLimitRead →
        PkgSig bundle uniformLimitRead pkg →
          UnaryHistory interval ∧ UnaryHistory polynomial ∧ UnaryHistory uniformError ∧
            Cont uniformError provenance uniformLimitRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle uniformLimitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier uniformLimitRoute uniformLimitPkg
  obtain ⟨intervalUnary, _continuousMapUnary, _errorUnary, polynomialUnary, _samplesUnary,
    _modulusUnary, uniformErrorUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  exact
    ⟨intervalUnary, polynomialUnary, uniformErrorUnary, uniformLimitRoute, provenancePkg,
      uniformLimitPkg⟩

theorem WeierstrassApproximationPolynomialModulusLedger [AskSetup] [PackageSetup]
    {interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName sampleRead polynomialRead errorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassApproximationCarrier interval continuousMap error polynomial samples modulus
        uniformError transport replay provenance localName bundle pkg →
      Cont samples modulus sampleRead →
        Cont sampleRead polynomial polynomialRead →
          Cont polynomialRead uniformError errorRead →
            PkgSig bundle errorRead pkg →
              UnaryHistory samples ∧ UnaryHistory modulus ∧ UnaryHistory sampleRead ∧
                UnaryHistory polynomial ∧ UnaryHistory polynomialRead ∧
                  UnaryHistory uniformError ∧ UnaryHistory errorRead ∧
                    Cont samples modulus sampleRead ∧
                      Cont sampleRead polynomial polynomialRead ∧
                        Cont polynomialRead uniformError errorRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle errorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier samplesModulusRead samplePolynomialRead polynomialErrorRead errorReadPkg
  obtain ⟨_intervalUnary, _continuousMapUnary, _errorUnary, polynomialUnary, samplesUnary,
    modulusUnary, uniformErrorUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have sampleReadUnary : UnaryHistory sampleRead :=
    unary_cont_closed samplesUnary modulusUnary samplesModulusRead
  have polynomialReadUnary : UnaryHistory polynomialRead :=
    unary_cont_closed sampleReadUnary polynomialUnary samplePolynomialRead
  have errorReadUnary : UnaryHistory errorRead :=
    unary_cont_closed polynomialReadUnary uniformErrorUnary polynomialErrorRead
  exact
    ⟨samplesUnary, modulusUnary, sampleReadUnary, polynomialUnary, polynomialReadUnary,
      uniformErrorUnary, errorReadUnary, samplesModulusRead, samplePolynomialRead,
      polynomialErrorRead, provenancePkg, errorReadPkg⟩

theorem WeierstrassApproximationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName sampleRead certRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassApproximationCarrier interval continuousMap error polynomial samples modulus
        uniformError transport replay provenance localName bundle pkg →
      Cont samples modulus sampleRead →
        Cont sampleRead uniformError certRead →
          PkgSig bundle certRead pkg →
            SemanticNameCert
                (fun row : BHist => (hsame row certRead ∨ hsame row localName) ∧
                  UnaryHistory row)
                (fun row : BHist =>
                  hsame row interval ∨ hsame row continuousMap ∨ hsame row error ∨
                    hsame row polynomial ∨ hsame row samples ∨ hsame row modulus ∨
                      hsame row uniformError ∨ hsame row transport ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row localName ∨
                          hsame row sampleRead ∨ hsame row certRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont samples modulus sampleRead ∧
                    Cont sampleRead uniformError certRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle certRead pkg)
                hsame ∧ UnaryHistory certRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier samplesModulusRead sampleErrorRead certReadPkg
  obtain ⟨_intervalUnary, _continuousMapUnary, _errorUnary, _polynomialUnary,
    samplesUnary, modulusUnary, uniformErrorUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, provenancePkg, localNamePkg⟩ := carrier
  have sampleReadUnary : UnaryHistory sampleRead :=
    unary_cont_closed samplesUnary modulusUnary samplesModulusRead
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed sampleReadUnary uniformErrorUnary sampleErrorRead
  let sourceSpec : BHist → Prop :=
    fun row : BHist => (hsame row certRead ∨ hsame row localName) ∧ UnaryHistory row
  let patternSpec : BHist → Prop :=
    fun row : BHist =>
      hsame row interval ∨ hsame row continuousMap ∨ hsame row error ∨
        hsame row polynomial ∨ hsame row samples ∨ hsame row modulus ∨
          hsame row uniformError ∨ hsame row transport ∨ hsame row replay ∨
            hsame row provenance ∨ hsame row localName ∨ hsame row sampleRead ∨
              hsame row certRead
  let ledgerPolicy : BHist → Prop :=
    fun row : BHist =>
      UnaryHistory row ∧ Cont samples modulus sampleRead ∧
        Cont sampleRead uniformError certRead ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg ∧ PkgSig bundle certRead pkg
  have core : NameCert sourceSpec hsame := by
    exact
      { carrier_inhabited := ⟨certRead, Or.inl (hsame_refl certRead), certReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row next same
          exact hsame_symm same
        equiv_trans := by
          intro row next final sameRowNext sameNextFinal
          exact hsame_trans sameRowNext sameNextFinal
        carrier_respects_equiv := by
          intro row next sameRowNext sourceRow
          cases sameRowNext
          exact sourceRow }
  have pattern_sound : ∀ {row : BHist}, sourceSpec row → patternSpec row := by
    intro row sourceRow
    cases sourceRow.left with
    | inl sameCert =>
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr sameCert)))))))))))
    | inr sameLocal =>
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl sameLocal))))))))))
  have ledger_sound : ∀ {row : BHist}, sourceSpec row → ledgerPolicy row := by
    intro row sourceRow
    exact
      ⟨sourceRow.right, samplesModulusRead, sampleErrorRead, provenancePkg, localNamePkg,
        certReadPkg⟩
  exact
    And.intro
      { core := core, pattern_sound := pattern_sound, ledger_sound := ledger_sound }
      certReadUnary

end BEDC.Derived.WeierstrassApproximationUp
