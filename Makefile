COQC = coqc -R ../../../ssrcorn/math-classes/src -as MathClasses -R ../../../ssrcorn -as CoRN

all : icreate.vo train.vo CartCR.vo
train.vo : train.v ROSCyberPhysicalSystem.vo
	$(COQC) $<
Everything.vo  : Everything.v
	$(COQC) $<


ROSCyberPhysicalSystem.vo : ROSCyberPhysicalSystem.v roscore.vo CoList.vo
	$(COQC) $<

%.vo : %.v
	$(COQC) $<

CoList.vo : CoList.v
	$(COQC) $<
		

icreate.vo : icreate.v ROSCyberPhysicalSystem.vo Vector.vo CartCR.vo MCInstances.vo
	$(COQC) $<

roscore.vo : roscore.v Process.vo
	$(COQC) $<

Process.vo : Process.v core.vo
	$(COQC) $<


ADC.vo : ADC.v core.vo
	$(COQC) $<

core.vo : core.v CoRNMisc.vo ContField.vo StdlibMisc.vo
	$(COQC) $<

Fin.vo : Fin.v StdlibMisc.vo
	$(COQC) $<

Vector.vo : Vector.v Fin.vo
	$(COQC) $<

ContField.vo : ContField.v PointWiseRing.vo SubCRing.vo CoRNMisc.vo
	$(COQC) $<

StdlibMisc.vo : StdlibMisc.v
	$(COQC) $<

CoRNMisc.vo : CoRNMisc.v CanonicalNotations.vo
	$(COQC) $<

CartCR.vo : CartCR.v IRLemmasAsCR.vo
	$(COQC) $<

IRLemmasAsCR.vo : IRLemmasAsCR.v IRTrig.vo CanonicalNotations.vo

%.tex: %.v %.vo
	$(COQC) $<
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)	


clean:
	rm *.vo *.glob
