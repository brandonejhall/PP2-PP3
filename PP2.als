//IMPORTS
open util/relation 
open util/ternary

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
	measures: one PerceptType,
	linked : some Sensor,
	placement : one Area,
}

sig PerceptType{
	type : one Percepts, 
	coloured: one Colour
}

sig Pipe{
	controlled: Valve
}

sig Controller{}

//END OF SIGNATURES

//ENUMERATIONS

enum Percepts {temperature,moisture,sunlight,humidity}
enum PerceptLevels{Low,Med,High}
enum irrigationType{drip,sprinkler,misting}
//enum ReservoirWaterLevel { empty, moderate, full }
enum ValvePosition{ opened , closed}
//enum ElevationLevel { below_sea_level,at_sea_level, above_sea_level  }
enum LandSize{small,mid,large}
enum Colour { Red, Green, Blue, Yellow }


//END OF ENUMERATIONS


//FACTS


fact GraphColouringOfNetworkOfSensorsInAnArea{

// if two sensors have the same percept type that means they have the same colour
all disj s,x: Sensor  | (s.measures.type = x.measures.type) => (s.measures.coloured = x.measures.coloured) 

// if two sensors are linked they are not the same color
 all disj s1, s2 : Sensor | s2 in s1.linked  => not(s1.measures.coloured = s2.measures.coloured)

//links between sensors are mutual
symmetric[linked]

// sensor is not linked to itself
all s: Sensor | not (s in s.linked)


//if two sensors are linked they are in the same area
all s: Sensor | all x: s.linked | s.placement = x.placement

// All percepts are in an area
all a: Area, p:Percepts| p in a.sensors.measures.type 

//different percepts have different colours
 all disj p1,p2: PerceptType | not(p2.type = p1.type) implies not(p1.coloured = p2.coloured)


//all sensors with different colours are connected
all disj s,j:Sensor | all a:Area | ( ((s+j) in a.sensors) and not(s.measures.coloured = j.measures.coloured)) implies j in s.linked and s in j.linked


}



// END OF FACTS

//PREDICATE
pred system1[]{some Area some Valve some CropType some Sensor some Pipe some Controller

#Area > 2}
run system1 for 4 expect 1

//END OF PREDICATE
