// Irrigation System Project
// Members: Twanda-Lee Briscoe, Brandon Hall, Zaria Chen Shui

//IMPORTS

open util/relation 
open util/ternary
open util/graph[Pipe]
open util/graph[Levels]
open util/boolean

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
	watching: set Sensor,
	notify: lone MainAccessPoint
}

sig Levels in PerceptLevels{
 inOrder : set Levels,
}

sig PerceptReading{
	var higherReading: set Levels, //lone
	var level: set Levels //one
}


sig Reservoir{
	distributesTo: one Pipe
}

sig Valve{
	var positioned : set ValvePosition, //one
	var intervene : set InterventionType //lone
}


sig CropType{
	required: PerceptType -> Levels,
	requiredPorosity : one SoilPorosity
}

sig Sensor{
	measures: one PerceptType,
	linked : some Sensor,
	placement : one Area,
	var measurement : set PerceptReading // one
}



sig PerceptType{
	type : one Percepts, 
	coloured: one Colour,
	intervention:  one InterventionType
}

sig Pipe{
	fittedWith: one Valve,
	connectedTo: set Pipe,
	irrigates : one Area
}

one sig MainAccessPoint in AccessPoint{
	controls : one Reservoir
	}

//END OF SIGNATURES
//MUTABLE FACTS

fact invMutable{
	always all v:Valve | one v.positioned and lone v.intervene
	
	always all s: Sensor | one s.measurement
	
	always all disj s,e:Sensor | s.measurement = e.measurement => s = e
	
	always all s:Sensor.measurement | one s.level and lone s.higherReading and s.higherReading = getHigherLevels[s.level]

	always all p:PerceptReading | (p in Sensor.measurement) => one p.level 

	always all p:PerceptReading | (p in Sensor.measurement) => p.higherReading = getHigherLevels[p.level]

	always all v:Valve | v.positioned = closed => no ( InterventionType & v.intervene)
	

}


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

//SEQUENCE OF PERCEPT LEVELS
fact SequenceOfLevels{
	treeRootedAt[inOrder, Levels]
	eq[#roots[inOrder],1]
	eq[#leaves[inOrder],1]
	all lev : innerNodes[inOrder] | one lev.inOrder
	Low in roots[inOrder]
	Med in innerNodes[inOrder]
	High in leaves[inOrder]
	

}

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

	all s:Sensor | no (s.measurement & (Sensor-s).measurement)
}
// this creates the star between the seperate access points in the system 
fact SystemStar{
	all mp : MainAccessPoint | (notify.mp) = (Area.point)-mp

	// all sensors in an area will be watched by a single acces point
	all a: Area |one ap: AccessPoint |ap.watching = a.sensors and ap in a.point

	// all access points are controlled by main access point
	//all ap: AccessPoint |one map:MainAccessPoint| ap in map.controls

	//There is only one Main AccessPoint in the system
	one MainAccessPoint
	
	// there is a Main access point which cotnrols all access points in the system
	//all a: AccessPoint | one map: MainAccessPoint | a in map.controls
	
	//if the areas are not the same  it means they cannot havethe same access points
	all a1, a2: Area | a1 != a2 => a1.point != a2.point
	
	//if an access point is in an area this means that the access point is watching all sensors in that area
	all ap: AccessPoint, a: Area | ap in a.point => ap.watching = a.sensors
	
	//sensors do not share between areas
	all disj a1, a2: Area, s: Sensor | s in a1.sensors and s in a2.sensors implies a1 = a2
	
	//if access point is watching the sensors of that area this mean that the acess point is an access point of that area
	all a : AccessPoint, a1: Area| a1.sensors = a.watching => a = a1.point
	all a: AccessPoint | a in ran[point]
	// if access point is controlled by main access point this means that the access point is associated with an area
	//all map: MainAccessPoint, ap: AccessPoint | ap in map.controls => ap in Area.point
	
	// all sensors must be placed in the area it is related to
	placement = ~sensors
}

fact CropTypes {
	//CropType Require only 4 percepts
	eq[#CropType.required,4]
	// All percepts are in an cropType
	all c: CropType, p:Percepts| p in dom[c.required].type
}

fact perceptTypeConstraints{
	// Each percept type has one colour
	all c: Colour | one p1: PerceptType | p1.coloured = c
}

fact Interventions {
	// When all readings are as required for each croptype, valve must be closed
	//all s: Sensor, c: CropType, a: Area | (s.measures -> s.measurement.level in c.required) implies ((irrigates.a).fittedWith.positioned = closed)
	
	// When some readings are lower than is required, valve must be opened
	//some s: Sensor, c: CropType, a: Area | (s.measures -> s.measurement.level not in c.required and (s.measurement.level not in s.measurement.higherReading.level) implies (irrigates.a).fittedWith.positioned = opened)
}


fact GraphOfPipes {
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
	//If there are multiple areas then pipes will be connected
	gt[#beside,0] => Pipe = ran[connectedTo]
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
	// if there are more than one area then areas must be beside an area
	gt[#Area,1] => Area = ran[beside]
}



// END OF FACTS

//PREDICATES FOR PP2
//TURN OFF OVERFLOW PROTECTION FOR LARGE PREDICATES TO GENERATE AN INSTANCE
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
run SensorReadingsRequireIntervention for 4 expect 1

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
run AllAreasHaveADifferentSizeAndDifferentSoilPorosity for 27

pred GraphOfSensorsExample{
	one a:Area | a.size  = mid

}

run GraphOfSensorsExample for 12


pred GraphOfPipes{
	all a:Area | a.size  = small
	#Area = 3
	
}
run GraphOfPipes for 12


pred SomeReadingsAreSuitableAndOthersAreNot[]{
	some Area
	some Sensor
	some CropType
	some Pipe
	some Valve
	some PerceptReading
	//one a: Area | a.size = large
	//when there is a set of sensors of the same type of the same area giving different readings some readings will cause and intervention and others will not.
	all s: Sensor, a: Area, c: CropType | (s in a.point.watching - s) implies (s.measures -> s.measurement.level not in c.required)

}
run SomeReadingsAreSuitableAndOthersAreNot for 4

pred StarOfAccessPoint[]{
#Area = 2
}run StarOfAccessPoint for 8



//END OF PREDICATES FOR PP2

// FUNCTIONS

fun getHigherLevels[lev: Levels]: Levels {lev.^inOrder - lev}


// this function returns the area if an intervention is required otherwise it returns all areas excluding the one passed if not interventions are required
fun interventionRequired[area:Area,pt:PerceptType]: Area{

	let allSensors = {x: Sensor| x in area.sensors and x.measures = pt} |
	let subOptimal = {x: Sensor |some y:PerceptLevels| x in allSensors and y in (x.measurement.level & (Levels - (area.planted.required[pt])))} |
	
	#subOptimal > (#subOptimal - #allSensors) => area else Area - area

}
// This function returns the sb optimal sensors in an area
fun subOptimalSensors[area:Area]: Sensor{
	let allSensors = {x: Sensor| x in area.sensors} |
	{x: Sensor | x in allSensors and no (area.planted.required[x.measures] & x.measurement.level)   }

}



//RUN STATEMENTS FOR PP3 


pred OneSensorBecomeOptimal{ 
one Area
historically all a:Area | #subOptimalSensors[a]  = 1

some area:Area,sensor:Sensor,interType:InterventionType,pt : PerceptType,pipe:Pipe| some disj pro,prn:PerceptReading |  
	StartingIntervention[area, pt , interType] or 
	ChangeToOptimalValue[pro, prn, sensor, area,pipe] or 
	StopIntervention[area,pt]

always eventually  (all a:Area,v:Valve | #subOptimalSensors[a] = 0 and v.positioned = closed) or stutter
}




run OneSensorBecomeOptimal   for 6 but 10 steps expect 1 



pred AllSensorsBecomeOptimal{ 
#Area = 2
all a:Area | gt[#subOptimalSensors[a],0] 

some area:Area,sensor:Sensor,interType:InterventionType,pt : PerceptType,pipe:Pipe| some disj pro,prn:PerceptReading |  
	StartingIntervention[area, pt , interType] or 
	ChangeToOptimalValue[pro, prn, sensor, area,pipe] or 
	StopIntervention[area,pt]

eventually  all a:Area| eq[#subOptimalSensors[a],0] 
}


run AllSensorsBecomeOptimal  for 12 but 30 steps expect 1 


pred ValvesWillOpen{ 
one Area
all a:Area | gt[#subOptimalSensors[a],0] 

some area:Area,sensor:Sensor,interType:InterventionType,pt : PerceptType,pipe:Pipe| some disj pro,prn:PerceptReading |  
	StartingIntervention[area, pt , interType] or 
	ChangeToOptimalValue[pro, prn, sensor, area,pipe] or 
	StopIntervention[area,pt]

eventually  all v:Valve| v.positioned = opened 
}


run ValvesWillOpen  for 4 but 4 steps expect 1 


pred ValvesWillCloseAndEveryThingIsOptimal{ 
one Area
all a:Area | gt[#subOptimalSensors[a],0] 

some area:Area,sensor:Sensor,interType:InterventionType,pt : PerceptType,pipe:Pipe| some disj pro,prn:PerceptReading |  
	StartingIntervention[area, pt , interType] or 
	ChangeToOptimalValue[pro, prn, sensor, area,pipe] or 
	StopIntervention[area,pt]

eventually  all area:Area,pt:PerceptType | StopIntervention[area,pt] 
}


run ValvesWillCloseAndEveryThingIsOptimal  for 4 but 10 steps expect 1 







//OPERATIONS
// STUTTER EVENT
pred stutter{

	all a:Area,pt :PerceptType  | not a in interventionRequired[a,pt]
	positioned' = positioned
	intervene' = intervene
	higherReading' =  higherReading  
	measurement' =  measurement
	level' = level
}
// THIS STARTS AN INTERVENTION BY OPENING VALVE AND ATTACHING COORECT INTERVENTION
pred StartingIntervention[area: Area, pt : PerceptType, interType:InterventionType]{
	//PRECONDITIONS
	#area = 1
	#interType = 1
	#pt = 1
	// intervention needed for this area
	area in interventionRequired[area,pt]
	//  valve is closed
	irrigates.area.fittedWith.positioned = closed
	// no current intervention taking place on area
	no irrigates.area.fittedWith.intervene & InterventionType 
	// intervention type is the one required
	interType in dom[Area.planted.required].intervention
	
	//POSTCONDITIONS
	
	positioned' =(positioned - irrigates.area.fittedWith -> ValvePosition) + irrigates.area.fittedWith -> opened

	intervene' = intervene + irrigates.area.fittedWith -> interType

	//FRAMECONDITIONS
	
	higherReading' =  higherReading  
 	
	measurement' =  measurement

	level' = level

}
// THIS CHANGES THE INTERVENTION TYPE TO THE OPTIMAL VALUE
pred ChangeToOptimalValue[oldReading:PerceptReading, newReading: PerceptReading, sensor:Sensor, land:Area,pipe:Pipe]{
	oldReading != newReading
	// sensor is in land passed to function
	sensor in land.sensors
	
	// reading in measurement of that sensor
	oldReading in sensor.measurement

	//does not have a higher level yet
	no newReading.higherReading & Levels
	// does not have a reading yet
	no newReading.level & PerceptLevels
	//pipe irrigates area passed
	land in pipe.irrigates
	
	//valve is open
	pipe.fittedWith.positioned = opened
	
	// some intervention is taking place
	gt[#pipe.fittedWith.intervene,0]
	
	//some a:Area| (not a.sensors.measurement.level in ran[a.planted.required]) 
	//current sensor measurment is not the required reading for the cropType
	sensor in subOptimalSensors[land]
	//not (sensor.measurement.level = land.planted.required[sensor.measures])

	
	//POST CONDITIONS

	higherReading' =  (higherReading - (oldReading -> oldReading.higherReading)) + newReading -> getHigherLevels[land.planted.required[sensor.measures]]  	
	level' = (level - (oldReading -> oldReading.level)) + (newReading -> land.planted.required[sensor.measures])
	measurement' =  (measurement - (sensor -> oldReading)) + (sensor -> newReading)
		
	//FRAME CONDITIONS
	positioned' = positioned
	intervene' = intervene
}
// THIS COMPLETELY STOPS THE INTERVENTION WHEN EVERYTHING IS OPTIMAL
pred StopIntervention[area:Area,pt:PerceptType]{
	// valve is open
	all p:irrigates.area | p.fittedWith.positioned = opened
	// an intervention is taking place by the valve
	all p:irrigates.area | p.fittedWith.intervene in InterventionType
	//no intervention required
	not area in interventionRequired[area,pt]
	//current intervention is related to the cropType
	 irrigates.area.fittedWith.intervene in dom[area.planted.required].intervention
	//POST CONDITIONS
	positioned' = (positioned - irrigates.area.fittedWith -> ValvePosition) + irrigates.area -> closed
	intervene' = intervene -  irrigates.area.fittedWith -> InterventionType
	//FRAME CONDITIONS
	higherReading' =  higherReading  
	measurement' =  measurement
	level' = level
}


fact {
	  (stutter or  
	some area: Area, pt : PerceptType, interType:InterventionType | StartingIntervention[area, pt , interType] or 
	some area:Area,sensor:Sensor,pipe:Pipe, pro,prn:PerceptReading | ChangeToOptimalValue[pro, prn, sensor, area,pipe] or 
	some area: Area, pt : PerceptType| StopIntervention[area,pt] 	)
}

//run ToStartAnIntervention{eventually (one i:InterventionType| opened in  ran[positioned] and i in ran[intervene])} for 4 expect 1
//run ToOptimize {some area:Area,sensor:Sensor,pipe:Pipe| some disj pro,prn:PerceptReading | ChangeToOptimalValue[pro, prn, sensor, area,pipe]} for 4 expect 1
//run ToOptimize {historically some a:Area| (not a.sensors.measurement.level in ran[a.planted.required]) implies eventually (all  a:Area|  a.sensors.measurement.level in ran[a.planted.required])} for 4  expect 1
//run ToOptimize {historically some a:Area| (not a.sensors.measurement.level in ran[a.planted.required]) =>  eventually (all  a:Area|  a.sensors.measurement.level in ran[a.planted.required])} for 4  expect 1
//run ToStopAnIntervention{ eventually (all  a:Area |  a.sensors.measurement.level in ran[a.planted.required] and no (InterventionType & ran[intervene]) and (irrigates.a).fittedWith.positioned = closed)} for 4 but 3 steps
// ASSERTIONS 
assert StartingInterventionAssertion
{	
	  always eventually all area: Area, pt : PerceptType, interType:InterventionType|all v:Valve | 
		(area in interventionRequired[area,pt]) and (subOptimalSensors[area] in Sensor) and v.positioned = closed 
			implies ( always eventually StartingIntervention[area,pt,interType])
}
check StartingInterventionAssertion for 4 but  2 steps expect 0

assert ChangeToOptimalAssertion
{	
	 always eventually some area:Area,sensor:Sensor,pipe:Pipe, pro,prn:PerceptReading , pt:PerceptType|some v:Valve | 
		(area in interventionRequired[area,pt]) and Sensor in subOptimalSensors[area] and v.positioned = opened
			implies (always eventually ChangeToOptimalValue[pro, prn, sensor, area,pipe])
}
check ChangeToOptimalAssertion for 4 but 5 steps expect 0

assert StopInterventionAssertions
{
	 always eventually some area: Area, pt : PerceptType| all v:Valve | 
		not (area in interventionRequired[area,pt]) and not (subOptimalSensors[area] in Sensor) and (v.positioned = opened)
			implies (always eventually StopIntervention[area,pt])
}

check StopInterventionAssertions for 4 expect 0
