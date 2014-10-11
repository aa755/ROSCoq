train.vo : train.v ROSCyberPhysicalSystem.vo trainDevs.vo
	coqc $<


ROSCyberPhysicalSystem.vo : ROSCyberPhysicalSystem.v roscore.vo CoList.vo
	coqc $<


CoList.vo : CoList.v
	coqc $<
	
trainDevs.vo : trainDevs.v Process.vo
	coqc $<
	

roscore.vo : roscore.v Process.vo
	coqc $<

Process.vo : Process.v core.vo
	coqc $<


ADC.vo : ADC.v core.vo
	coqc $<

core.vo : core.v
	coqc $<

%.tex: %.v
	coqc $<
	coqdoc   -l --latex --interpolate --body-only $< -o $(@)	
