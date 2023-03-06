//SIGNATURES

sig Area {

measuredAt: one LandSize,
tempMeasuredAt: one PerceptLevels,
moistureLevel: one PerceptLevels , 
sunLevel: one PerceptLevels,
humidityLevel: one PerceptLevels,
elevation : one PerceptLevels,
beside: some Area,
irrigatedWith : some Pipe,
sensors : set Sensor,
controller : one Controller,
planted : one CropType


}

sig AccessPoint{}


sig Resevoir{}

sig Valve{
	postioned : one ValvePosition
}

sig Size,Elevation{}

sig CropType{
	tempRequired: one PerceptLevels,
	moistureLevelRequired: one PerceptLevels, 
	sunLeveRequiredl: one PerceptLevels,
	humidityLeveRequiredl: one PerceptLevels
}
sig Sensor{
	percept: one PerceptType,
	linked : some Sensor,
	placement : one Area,
	coloured : one Colour
	

}

sig Pipe{
	controlled: Valve}

sig Controller{}

//END OF SIGNATURES

//ENUMERATIONS

enum PerceptType {temperature,moisture,sunlight,humidity}
enum PerceptLevels{Low,Med,High}
enum irrigationType{drip,sprinkler,misting}
//enum ReservoirWaterLevel { empty, moderate, full }
enum ValvePosition{ opened , closed}
//enum ElevationLevel { below_sea_level,at_sea_level, above_sea_level  }
enum LandSize{small,mid,large}
enum Colour { Red, Green, Blue, Yellow }


//END OF ENUMERATIONS


//FACTS


fact{

// if two sensors have the same percept type that means they have the same colour
all disj s,x: Sensor  | (s.percept = x.percept ) => (s.coloured = x.coloured) 

// of two sensors are linked they are not the same color
all disj s,x: Sensor | s.placement = x.placement and (x in s.linked or s in x.linked) => not(s.coloured in x.coloured)

// sensor is no it linked to itself
all s: Sensor | not (s in s.linked)


//if two sensors are linked they are in the same area
all s: Sensor | all x: s.linked | s.placement = x.placement


all a: Area, p:PerceptType| p in a.sensors.percept 

all disj s1, s2: Sensor | s1.coloured != s2.coloured => s1 in s2.*linked or s2 in s1.*linked

//all disj a1, a2 : Area | not (a1.sensors in a2.sensors)

}


// END OF FACTS

//PREDICATE
pred system1[]{some Area some Valve some CropType some Sensor some Pipe some Controller

#Area > 2}
run system1 for 4 expect 1

//END OF PREDICATE
