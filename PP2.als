// Irrigation System Project
// Members: Twanda-Lee Briscoe, Brandon Hall, Zaria Chen Shui

//IMPORTS
open util/relation 
open util/ternary
open util/graph[Pipe]
//SIGNATURES

sig Area {
	size: one LandSize,
	landPorosity: one SoilPorosity,
	beside: set Area,
	sensors : set Sensor,
	planted : one CropType,
	point : one AccessPoint
}

sig AccessPoint{
	watching: set Sensor
}


sig Reservoir{
	distributesTo: one Pipe
}

sig Valve{
	positioned : one ValvePosition
}


sig CropType{
	required: PerceptType -> PerceptLevels,
	requiredPorosity : one SoilPorosity
}
sig Sensor{
	measures: one PerceptType,
	linked : some Sensor,
	placement : one Area,
	measurement : one PerceptReading
}

sig PerceptReading{
	higherReading: lone PerceptReading,
	level: one PerceptLevels
} {
 all m, n: PerceptReading | m.@higherReading = n.@higherReading implies m = n
 some lev: PerceptReading | lev.^@higherReading = PerceptReading - lev 
}

sig PerceptType{
	type : one Percepts, 
	coloured: one Colour,
	//intervention:  one InterventionType
}

sig Pipe{
	fittedWith: one Valve,
	connectedTo: set Pipe,
	irrigates : one Area
}

sig MainAccessPoint{
	controls: set AccessPoint}

//END OF SIGNATURES


//ENUMERATIONS

enum Percepts {temperature,moisture,sunlight,humidity}
enum PerceptLevels{Low,Med,High}
enum InterventionType{drip,sprinkler,misting,manual}
enum ValvePosition{ opened , closed}
enum LandSize{small,mid,large}
enum SoilPorosity{loose,compacted,normal}
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
}

// this creates the star between the seperate access points in the system 
fact SystemStar{
	// all sensors in an area will be watched by a single acces point
	all a: Area |one ap: AccessPoint |ap.watching = a.sensors and ap in a.point

	// all access points are controlled by main access point
	all ap: AccessPoint |one map:MainAccessPoint| ap in map.controls

	//There is only one Main AccessPoint in the system
	one MainAccessPoint
	
	// there is a Main access point which cotnrols all access points in the system
	all a: AccessPoint | one map: MainAccessPoint | a in map.controls
	
	//if the areas are not the same  it means they cannot havethe same access points
	all a1, a2: Area | a1 != a2 => a1.point != a2.point
	
	//if an access point is in an area this means that the access point is watching all sensors in that area
	all ap: AccessPoint, a: Area | ap in a.point => ap.watching = a.sensors
	
	//sensors do not share between areas
	all disj a1, a2: Area, s: Sensor | s in a1.sensors and s in a2.sensors implies a1 = a2
	
	//if access point is watching the sensors of that area this mean that the acess point is an access point of that area
	all a : AccessPoint, a1: Area| a1.sensors = a.watching => a = a1.point
	
	// if access point is controlled by main access point this means that the access point is associated with an area
	all map: MainAccessPoint, ap: AccessPoint | ap in map.controls => ap in Area.point
	
	// all sensors must be placed in the area it is related to
	placement = ~sensors
}

fact CropTypes {
	// All percepts are in an cropType
	all c: CropType, p:Percepts| p in dom[c.required].type
}

fact perceptTypeConstraints{
	// Each percept type has one colour
	all c: Colour | one p1: PerceptType | p1.coloured = c
}

fact Interventions {
	// When all readings are as required for each croptype, valve must be closed
	all s: Sensor, c: CropType, a: Area | (s.measures -> s.measurement.level in c.required) implies ((irrigates.a).fittedWith.positioned = closed)
	
	// When some readings are lower than is required, valve must be opened
	some s: Sensor, c: CropType, a: Area | (s.measures -> s.measurement.level not in c.required and (s.measurement.level not in s.measurement.higherReading.level) implies (irrigates.a).fittedWith.positioned = opened)
}

fact DirectedGraphOfPipes {
	// if a pipe is connected to another then it does not irrigate the same area  and the areas they irrigate are beside each other
	all disj p1, p2: Pipe | p2 in p1.connectedTo implies no(p2.irrigates & p1.irrigates) and (p1.irrigates in p2.irrigates.beside)
	
	// if a pipe irrigates an area then that pipe is the only pipe in that area
	all p1, p2:Pipe | (p1.irrigates = p2.irrigates) => p1 = p2
	
	//pipe cannot be connected to itself
	no (iden & connectedTo)
	
	// all areas are irrigated by some pipe
	all a : Area | a in Pipe.irrigates
	
	// each pipe is fitted with a single unique valve
	all p1 ,p2: Pipe | (p1.fittedWith = p2.fittedWith) => p1 = p2
	
	// All valves in the system must be fitted to a pipe
	all v: Valve | v in ran[fittedWith]
	
	// All pipes that are not attached to the reservoir are connected to another pipe
	all p: Pipe | p in p.*connectedTo
}

fact constraints{
	// both areas are beside each other
	symmetric[beside]
	// if a pipe connection is mutual
	symmetric[connectedTo]
	//only one Reservoir in system
	one Reservoir
}

fact FactsAboutArea{
	//small areas have 4 sensors
	all a:Area | (a.size = small) => #a.sensors = 4
	//mid sized areas have 8 sensors
	all a:Area | (a.size = mid) => #a.sensors = 8
	//large areas have 12 sensors
	all a:Area | (a.size = large) => #a.sensors = 12
	// the crop planted in that area must match with the land's soil porosity
	all a:Area, ct: CropType|  ct in a.planted => ct.requiredPorosity = a.landPorosity
	//an area cannot be beside itself
	no (iden & beside)
	// All CropTypes in system must be planted in an area
	all c : CropType | c in ran[planted]
}

fact PerceptReading{
	#PerceptReading = 3
	one p: PerceptReading | p.level = Low
	one p: PerceptReading | p.level = Med
	one p: PerceptReading | p.level = High
	all p: PerceptReading | p.level = High => no (p & dom[higherReading])
	all p: PerceptReading | p.level = Low => no (p & ran[higherReading])
	no iden & higherReading
}

// END OF FACTS

//PREDICATE

pred SensorReadingsDontRequireIntervention[]{
	some Area 
	some Valve 
	some CropType 
	some Sensor 
	some Pipe 
	#Area = 1
	// All sensors within an area are receiving readings aligned with the level required for the crop type in that area.
	 all a: Area, s: Sensor | (s in a.point.watching) implies (s.measures -> s.measurement.level in a.planted.required)
}
run SensorReadingsDontRequireIntervention for 4 expect 1

pred SensorReadingsRequireIntervention[]{
	some Area 
	some Valve 
	some CropType 
	some Sensor 
	some Pipe 
	#Area = 1
	// All sensor readings show interventions interventions required for the crop type in that area.
	 all a: Area, s: Sensor, c: CropType | (s in a.point.watching) implies (s.measures -> s.measurement.level not in c.required )
}
//run SensorReadingsRequireIntervention for 4 expect 1

pred AllAreasHaveADifferentSizeAndDifferentSoilPorosity[]{
	one a: Area | a.size = small
	one a: Area | a.size = mid 
	one a: Area | a.size = large
	one a: Area | a.landPorosity = loose
	one a: Area | a.landPorosity = compacted 
	one a: Area | a.landPorosity = normal 
	all p : Pipe | p in Pipe.connectedTo
	one p : Pipe | p in Reservoir.distributesTo
}
// run AllAreasHaveADifferentSizeAndDifferentSoilPorosity for 27



//END OF PREDICATE
