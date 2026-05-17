import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_triple_composite_associativity [AskSetup] [PackageSetup]
    {source middle target final graph01 landing01 routes01 transport01 provenance01 cert01
      graph12 landing12 routes12 transport12 provenance12 cert12 graph23 landing23 routes23
      transport23 provenance23 cert23 composite01 composite12 tripleLeft tripleRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source middle graph01 landing01 routes01 transport01
        provenance01 cert01 bundle pkg ->
      CertificateCompilerCarrier middle target graph12 landing12 routes12 transport12
        provenance12 cert12 bundle pkg ->
        CertificateCompilerCarrier target final graph23 landing23 routes23 transport23
          provenance23 cert23 bundle pkg ->
          Cont landing01 graph12 composite01 ->
            Cont landing12 graph23 composite12 ->
              Cont composite01 graph23 tripleLeft ->
                Cont graph01 composite12 tripleRight ->
                  hsame tripleLeft tripleRight ->
                    UnaryHistory tripleLeft ∧ UnaryHistory tripleRight ∧
                      Cont landing01 graph12 composite01 ∧
                        Cont landing12 graph23 composite12 ∧
                          Cont composite01 graph23 tripleLeft ∧
                            Cont graph01 composite12 tripleRight ∧
                              hsame tripleLeft tripleRight ∧ PkgSig bundle cert01 pkg ∧
                                PkgSig bundle cert12 pkg ∧ PkgSig bundle cert23 pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier01 carrier12 carrier23 landing01Graph12Composite01
    landing12Graph23Composite12 composite01Graph23TripleLeft graph01Composite12TripleRight
    tripleSame
  obtain ⟨_sourceUnary, _middleUnary, graph01Unary, landing01Unary, _routes01Unary,
    _transport01Unary, _provenance01Unary, _sourceGraph01Landing01,
    _landing01Routes01Middle, _provenance01MiddleCert01, _cert01Endpoint, cert01Pkg⟩ :=
    carrier01
  obtain ⟨_middleUnary', _targetUnary, graph12Unary, landing12Unary, _routes12Unary,
    _transport12Unary, _provenance12Unary, _middleGraph12Landing12,
    _landing12Routes12Target, _provenance12TargetCert12, _cert12Endpoint, cert12Pkg⟩ :=
    carrier12
  obtain ⟨_targetUnary', _finalUnary, graph23Unary, _landing23Unary, _routes23Unary,
    _transport23Unary, _provenance23Unary, _targetGraph23Landing23,
    _landing23Routes23Final, _provenance23FinalCert23, _cert23Endpoint, cert23Pkg⟩ :=
    carrier23
  have composite01Unary : UnaryHistory composite01 :=
    unary_cont_closed landing01Unary graph12Unary landing01Graph12Composite01
  have composite12Unary : UnaryHistory composite12 :=
    unary_cont_closed landing12Unary graph23Unary landing12Graph23Composite12
  have tripleLeftUnary : UnaryHistory tripleLeft :=
    unary_cont_closed composite01Unary graph23Unary composite01Graph23TripleLeft
  have tripleRightUnary : UnaryHistory tripleRight :=
    unary_cont_closed graph01Unary composite12Unary graph01Composite12TripleRight
  exact
    ⟨tripleLeftUnary, tripleRightUnary, landing01Graph12Composite01,
      landing12Graph23Composite12, composite01Graph23TripleLeft,
      graph01Composite12TripleRight, tripleSame, cert01Pkg, cert12Pkg, cert23Pkg⟩

end BEDC.Derived.CertificateCompilerUp
