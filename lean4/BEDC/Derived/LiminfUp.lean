import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LiminfCarrier [AskSetup] [PackageSetup]
    (sequence lowerCut dyadic terminal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory sequence ∧ UnaryHistory lowerCut ∧ UnaryHistory dyadic ∧
    UnaryHistory terminal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont sequence lowerCut dyadic ∧
        Cont dyadic terminal replay ∧ PkgSig bundle provenance pkg

theorem LiminfCarrier_route_rows [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg ->
      Cont sequence lowerCut dyadic ∧ Cont dyadic terminal replay ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig LiminfCarrier
  intro carrier
  exact ⟨carrier.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.left,
    carrier.right.right.right.right.right.right.right.right.right.right⟩

theorem LiminfNameCertObligations [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      Cont terminal transport sealRead →
      PkgSig bundle sealRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead)
          (fun row : BHist => PkgSig bundle sealRead pkg ∧ hsame row sealRead)
          hsame ∧
        UnaryHistory sequence ∧ UnaryHistory lowerCut ∧ UnaryHistory dyadic ∧
          UnaryHistory terminal ∧ UnaryHistory sealRead ∧ Cont sequence lowerCut dyadic ∧
            Cont dyadic terminal replay ∧ Cont terminal transport sealRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier terminalTransport sealPkg
  have sequenceUnary : UnaryHistory sequence := carrier.left
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalTransport
  have sequenceRoute : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have terminalRoute : Cont dyadic terminal replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead)
          (fun row : BHist => PkgSig bundle sealRead pkg ∧ hsame row sealRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row other same
          exact hsame_symm same
        equiv_trans := by
          intro row other third sameRO sameOT
          exact hsame_trans sameRO sameOT
        carrier_respects_equiv := by
          intro row other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro row source
        exact ⟨sealPkg, source.left⟩
    }
  exact
    ⟨cert, sequenceUnary, lowerCutUnary, dyadicUnary, terminalUnary, sealUnary,
      sequenceRoute, terminalRoute, terminalTransport, provenancePkg, sealPkg⟩

theorem LiminfTailLowerEnvelopeCompatibility [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic upperEnvelope terminal transport replay provenance localName
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory upperEnvelope →
        Cont lowerCut upperEnvelope dyadic →
          Cont terminal transport sealRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row terminal) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperEnvelope ∨
                        hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont lowerCut upperEnvelope dyadic ∧
                        Cont terminal transport sealRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier upperEnvelopeUnary lowerUpperRoute terminalTransport provenancePkg sealPkg
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalTransport
  have lowerSource :
      (fun row : BHist =>
        (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row terminal) ∧
          UnaryHistory row) lowerCut := by
    exact ⟨Or.inl (hsame_refl lowerCut), lowerCutUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row terminal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperEnvelope ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut upperEnvelope dyadic ∧
              Cont terminal transport sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lowerCut lowerSource
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
          constructor
          · cases source.left with
            | inl sameLower =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameLower)
            | inr rest =>
                cases rest with
                | inl sameUpper =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameUpper))
                | inr sameTerminal =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTerminal))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameLower =>
            exact Or.inr (Or.inl sameLower)
        | inr rest =>
            cases rest with
            | inl sameUpper =>
                exact Or.inr (Or.inr (Or.inl sameUpper))
            | inr sameTerminal =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTerminal))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, lowerUpperRoute, terminalTransport, provenancePkg, sealPkg⟩
    }
  exact ⟨cert, sealUnary⟩

theorem LiminfTailCutRoute [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName sealRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      Cont terminal transport sealRead →
        Cont sealRead replay consumerRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
                      hsame row terminal ∨ hsame row sealRead ∨ hsame row consumerRead)
                  (fun row : BHist =>
                    PkgSig bundle localName pkg ∧ Cont sealRead replay consumerRead ∧
                      hsame row consumerRead)
                  hsame ∧
                UnaryHistory consumerRead ∧ Cont sequence lowerCut dyadic ∧
                  Cont dyadic terminal replay ∧ Cont terminal transport sealRead ∧
                    Cont sealRead replay consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier terminalSeal sealConsumer _provenancePkg localNamePkg
  have sequenceRoute : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have terminalRoute : Cont dyadic terminal replay :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have replayUnary : UnaryHistory replay := carrier.right.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalSeal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealUnary replayUnary sealConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row dyadic ∨
              hsame row terminal ∨ hsame row sealRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle localName pkg ∧ Cont sealRead replay consumerRead ∧
              hsame row consumerRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨localNamePkg, sealConsumer, source.left⟩
  }
  exact ⟨cert, consumerUnary, sequenceRoute, terminalRoute, terminalSeal, sealConsumer⟩

theorem LiminfTailEnvelopeMonotoneRefinement [AskSetup] [PackageSetup]
    {sequence lowerCut refinedLowerCut dyadic upperEnvelope terminal transport replay
      provenance localName sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory refinedLowerCut →
        Cont lowerCut refinedLowerCut upperEnvelope →
          Cont refinedLowerCut upperEnvelope dyadic →
            Cont terminal transport sealRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row refinedLowerCut ∨ hsame row dyadic ∨
                          hsame row terminal) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sequence ∨ hsame row lowerCut ∨
                          hsame row refinedLowerCut ∨ hsame row upperEnvelope ∨
                            hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont lowerCut refinedLowerCut upperEnvelope ∧
                          Cont refinedLowerCut upperEnvelope dyadic ∧
                            Cont terminal transport sealRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier refinedUnary lowerRefinementRoute refinedUpperRoute terminalTransport
    provenancePkg sealPkg
  have terminalUnary : UnaryHistory terminal := carrier.right.right.right.left
  have transportUnary : UnaryHistory transport := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed terminalUnary transportUnary terminalTransport
  have refinedSource :
      (fun row : BHist =>
        (hsame row refinedLowerCut ∨ hsame row dyadic ∨ hsame row terminal) ∧
          UnaryHistory row) refinedLowerCut := by
    exact ⟨Or.inl (hsame_refl refinedLowerCut), refinedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row refinedLowerCut ∨ hsame row dyadic ∨ hsame row terminal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row refinedLowerCut ∨
              hsame row upperEnvelope ∨ hsame row dyadic ∨ hsame row terminal ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont lowerCut refinedLowerCut upperEnvelope ∧
              Cont refinedLowerCut upperEnvelope dyadic ∧
                Cont terminal transport sealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refinedLowerCut refinedSource
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
          constructor
          · cases source.left with
            | inl sameRefined =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefined)
            | inr rest =>
                cases rest with
                | inl sameDyadic =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic))
                | inr sameTerminal =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTerminal))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameRefined =>
            exact Or.inr (Or.inr (Or.inl sameRefined))
        | inr rest =>
            cases rest with
            | inl sameDyadic =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDyadic))))
            | inr sameTerminal =>
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTerminal)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, lowerRefinementRoute, refinedUpperRoute, terminalTransport,
            provenancePkg, sealPkg⟩
    }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LiminfUp
