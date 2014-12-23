COQC = coqc -R ../../../ssrcorn/math-classes/src -as MathClasses -R ../../../ssrcorn -as CoRN

train.vo : train.v ROSCyberPhysicalSystem.vo
	$(COQC) $<
Everything.vo  : Everything.v
	$(COQC) $<


ROSCyberPhysicalSystem.vo : ROSCyberPhysicalSystem.v roscore.vo CoList.vo
	$(COQC) $<


CoList.vo : CoList.v
	$(COQC) $<
	
trainDevs.vo : trainDevs.v Process.vo
	$(COQC) $<
	

roscore.vo : roscore.v Process.vo
	$(COQC) $<

Process.vo : Process.v core.vo
	$(COQC) $<


ADC.vo : ADC.v core.vo
	$(COQC) $<

core.vo : core.v CoRNMisc.vo
	$(COQC) $<

CoRNMisc.vo : CoRNMisc.v
	$(COQC) $<

%.tex: %.v
	$(COQC) $<
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)	

clean:
	rm *.vo *.glob
