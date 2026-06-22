import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfScopedTailEnvelope [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead
      consumerRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      Cont terminal transport sealRead →
        Cont sealRead replay consumerRead →
          Cont lowerCut dyadic tailRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                        hsame row terminal ∨ hsame row sealRead ∨ hsame row consumerRead ∨
                          hsame row tailRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont lowerCut dyadic tailRead ∧
                        Cont terminal transport sealRead ∧ Cont sealRead replay consumerRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ Cont lowerCut dyadic tailRead ∧
                    Cont terminal transport sealRead ∧ Cont sealRead replay consumerRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier terminalSeal sealConsumer lowerDyadicTail provenancePkg localNamePkg
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed lowerCutUnary dyadicUnary lowerDyadicTail
  have tailSource :
      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row) tailRead := by
    exact ⟨hsame_refl tailRead, tailUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead ∨ hsame row consumerRead ∨
                hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut dyadic tailRead ∧
              Cont terminal transport sealRead ∧ Cont sealRead replay consumerRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro tailRead tailSource
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, lowerDyadicTail, terminalSeal, sealConsumer,
            provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, tailUnary, lowerDyadicTail, terminalSeal, sealConsumer⟩

end BEDC.Derived.LiminfUp
