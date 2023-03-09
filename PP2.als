//IMPORTS
open util/relation 
open util/ternary
open util/graph[Pipe]
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
planted : one CropType,
point : one AccessPoint


}{


}

sig AccessPoint{
 watching: set Sensor
}


sig Reservoir{}

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
	controlled: Valve,
	connectedTo: set Pipe,
	irrigates : Area
}

sig MainAccessPoint{
controls: set AccessPoint}

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

//SENSORS ARE CONNECTED VIA GRAPH COLOURING
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

//if sensor is in an ar
}

// this creates  the star between the seperate access points in the system 
fact SystemStar{
// all sensors in an area will be watched by a single acces point
all a: Area |one ap: AccessPoint |ap.watching = a.sensors and ap in a.point

all ap: AccessPoint |one map:MainAccessPoint| ap in map.controls

one MainAccessPoint

all a: AccessPoint | one map: MainAccessPoint | a in map.controls

all a1, a2: Area | a1 != a2 => a1.point != a2.point

all ap: AccessPoint, a: Area | ap in a.point => ap.watching = a.sensors

//sensors do not share between areas
all disj a1, a2: Area, s: Sensor | s in a1.sensors and s in a2.sensors implies a1 = a2

all a : AccessPoint, a1: Area| a1.sensors = a.watching => a = a1.point
}



fact DirectedTreeOfPipes {
// there exists a pipe that comes from no pipe but it must go to something(starting pipe)
one p:Pipe | no (connectedTo.p & Pipe) and some (p.connectedTo & Pipe)
// there exists some pipes that connects to no pipes but there exists some pipes it comes from(leaves)
some p:Pipe | no (p.connectedTo & Pipe) and some (connectedTo.p & Pipe)
// if a pipe is connected to another then it does not irrigate the same area  and the areas they irrigate are beside each other
all disj p1,p2: Pipe | p2 in p1.connectedTo implies no(p2.irrigates & p1.irrigates) and (p1.irrigates in p2.irrigates.beside)
//ensures pipe does not have cycles
acyclic[connectedTo,Pipe]
}


fact constraints{

symmetric[beside]
all s: Sensor | s in s.placement.sensors

}

// END OF FACTS

//PREDICATE
pred system1[]{some Area some Valve some CropType some Sensor some Pipe some Controller

}
run system1 for 8 expect 1

//END OF PREDICATE
