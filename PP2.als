sig Area {

measuredAt: Size,
tempMeasuredAt: Temperature,
mLevel: Moisture, 
sunLevel: Sunlight,
hLevel:Humidity,
beside: some Area,
irrigatedWith : set Pipe,
sensors : set Sensor

}

sig Resevoir{
	 contents  : one  waterLevel
}

sig Valve{
// isOpen: one univ
}

sig Size,Elevation,SoilPorosity,WaterLevel,PerceptType,Temperature,Moisture,Sunlight,Humidity,waterLevel{}

sig CropType{
tempRequired: one Temperature,
mLevelRequired: one Moisture, 
sunLeveRequiredl: one Sunlight,
hLeveRequiredl: one Humidity
}
sig Sensor{
	percept: one PerceptType,
	linked : Sensor,
	placement : Area
}

/*
fact{
let irrigationType = (0 -> "drip") + (1 -> "sprinkler") + (3 -> "misting")

}*/

fact{
one Resevoir
some Area
some sensors
}

sig Pipe{
controlled: Valve}

