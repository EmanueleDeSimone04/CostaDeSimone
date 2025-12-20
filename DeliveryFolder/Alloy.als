enum Status {Optimal, Medium, Sufficient, RequiresMaintenance}

enum Bool {True, False}

var abstract sig BikePath {
	var status: lone Status,
	var origin: lone StreetNode,
	var infoInserted:  one Bool,
	var published: one Bool
}

var sig ManuallyInsertedBikePath extends BikePath {
	var validatedByEGAS: one Bool
}

var sig AutomaticallyInsertedBikePath extends BikePath {
	var correctedByUser: one Bool,
	var confirmedByUser: one Bool
}

var sig StreetNode {
	var bikePath: one BikePath,
	var street: one Street,	
	var potholesDetected: lone PotholeNode,
	var end: one Bool,
	var nextStreet: lone StreetNode
}

sig Street {
	adjacentStreets: some Street,
	length: one Int
} {length > 0}

var sig PotholeNode {
	var isLast: one Bool,
	var streetNode: one StreetNode,
	var distanceFromOrigin: one Int,
	var nextPothole: lone PotholeNode
} {distanceFromOrigin > 0}

//in the initial instant the world is empty except for the streets that are always the same throughout all the states
fact initialState {
	no BikePath and no StreetNode and no PotholeNode
}

//this predicate is true when a BP has been created in the current instant
pred newlyCreatedBikePath[bp: BikePath] {
	(before bp not in BikePath) and bp in BikePath
}

//the only variable fields of StreetNode should be potholesDetected
fact streetNodeImmutability {
	always (all sn: StreetNode | ((after sn in StreetNode) implies (sn.bikePath = (sn.bikePath)' and sn.street = (sn.street)' and sn.end = (sn.end)'  and sn.nextStreet = (sn.nextStreet)')))
}

// the fields of PotholeNode are immutable
fact potholeNodeImmutability {
	always (all pn: PotholeNode | ((after pn in PotholeNode) implies (pn.isLast = (pn.isLast)' and pn.streetNode = (pn.streetNode)' and pn.distanceFromOrigin = (pn.distanceFromOrigin)'  and pn.nextPothole = (pn.nextPothole)')))
}

/* regarding the two facts above, I did not directly declare the fields static because of warnings given by the tool*/

//once created the bike path cannot disappear from the world
fact bikePathPermanence {
	always (all bp: BikePath |  (bp in ManuallyInsertedBikePath implies after bp in ManuallyInsertedBikePath) and
					    (bp in AutomaticallyInsertedBikePath implies after bp in AutomaticallyInsertedBikePath)
	)
}

//if a BP has just been created it has no information inserted in that instant
fact newlyCreatedBikePathConstraints {
	always (
		all bp: BikePath | (newlyCreatedBikePath[bp] implies (
			no bp.origin and no bp.status and bp.infoInserted = False and bp.published = False and
			((bp in ManuallyInsertedBikePath) implies bp.validatedByEGAS = False) and
			((bp in AutomaticallyInsertedBikePath) implies (bp.correctedByUser = False and bp.confirmedByUser = False))
		))
	)
}

//the predicate is true if the user has inserted info about the BikePath bp in manual mode and the EGAS has not approved it yet
pred infoInsertedManually[bp: BikePath] {
	bp in ManuallyInsertedBikePath and bp.infoInserted = True and bp.validatedByEGAS = False and bp.published = False
}

//the predicate is true if the user has inserted info about the BikePath bp in automated mode and has not approved or nor corrected the it yet
pred infoInsertedAutomatically[bp: BikePath] {
	bp in AutomaticallyInsertedBikePath and bp.infoInserted = True and bp.correctedByUser = False and bp.confirmedByUser = False and bp.published = False
}

//if a BP has just been created, then its only possible next state can be only one of the two mentioned above
fact infoInsertionStateConstraint {
	always ( all bp: BikePath | ( newlyCreatedBikePath[bp] implies after(infoInsertedManually[bp] or infoInsertedAutomatically[bp])))
}

pred infoInserted[bp: BikePath] {
	 infoInsertedManually[bp] or  infoInsertedAutomatically[bp]
}

//if a user has inserted information about the BP, then all the fields must have some kind of information (either correct or wrong) and the field infoInserted will always be True from then on
fact informationInsertedConstraint {
	always ( all bp: BikePath | ( infoInserted[bp] implies (
		#bp.status = 1 and #bp.origin = 1 and always bp.infoInserted = True
	)))
}

/************************** Street Constraints **************************/
// a StreetNode exists only if it is part of a list
fact streetNodeExistanceConstraint {
	always (all sn: StreetNode | (sn in sn.bikePath.origin.*nextStreet))
}

// if a street is the end of the path, then there is no next street. Moreover, each path should always end
fact pathEndingConstraint {
	always ( (all sn: StreetNode | (sn.end = True iff #sn.nextStreet = 0)) and (all bp: BikePath | bp.infoInserted = True implies (some sn: StreetNode | sn.bikePath = bp and sn.end = True)))
}

// each node of a list of street nodes should refer to the same BikePath and is already correct (adjacent streets and no repeated streets) if inserted through automated mode (becauese we assume that the GPS retrieves that kind of information correctly, the false positive can only be generated by sensors)
fact pathConstraint {
	always ((all bp: BikePath | #bp.origin = 1 implies bp.origin.bikePath = bp) and (all sn: StreetNode | (sn.end = False implies sn.bikePath = sn.nextStreet.bikePath) and			//each node of a list of the streets should refer to the same BikePath
		((sn.bikePath in AutomaticallyInsertedBikePath and sn.end = False) implies (sn.nextStreet.street in sn.street.adjacentStreets and								// a path must be formed by adjacent streets
		 sn.street not in sn.^nextStreet.street))																							// a path  must have no repeated streets in it
	))
}

// a street cannot be adjacent to itself and if s1 is adjacent to s2, then s2 is adjacent to s1
fact adjacencyConstraint {
	(all s: Street | s not in s.adjacentStreets) and
	(all s1, s2: Street | (s1 != s2 implies (s1 in s2.adjacentStreets iff s2 in s1.adjacentStreets)))
}

/************************** Potholes Constraints **************************/
// a PotholeNode exists only if it is part of a list
fact potholeNodeExistanceConstraint {
	always (all pn: PotholeNode | (pn in pn.streetNode.potholesDetected.*nextPothole))
}

// given a StreetNode sn, returns the set of all streets from sn1 up to sn2 (excluded)
fun streetsUpTo[sn1, sn2: StreetNode]: set Street {
    (sn1.*nextStreet - sn2.*nextStreet).street
}

// given a StreetNode sn, returns the sum of the lentgh of all the streets before sn in the BP
fun distanceFromOrigin(sn: StreetNode) : Int {
	sum streetsUpTo[sn.bikePath.origin, sn].length
}

// all potholes of a same StreetNode sn must refer to sn, must have a coherent distance from the origin and if it is the last on the list, it must not have a successor
fact potholeConstraints {
	always ( (all sn: StreetNode |  #sn.potholesDetected = 1 implies sn.potholesDetected.streetNode = sn) and (all pn: PotholeNode | (
		(pn.isLast = True iff #pn.nextPothole = 0) and
		(pn.isLast = False implies pn.nextPothole.streetNode = pn.streetNode) and
		(pn.distanceFromOrigin >= distanceFromOrigin[pn.streetNode] and pn.distanceFromOrigin < distanceFromOrigin[pn.streetNode] + pn.streetNode.street.length) and
		(pn.isLast = False implies  pn.nextPothole.distanceFromOrigin > pn.distanceFromOrigin)					// the potholes in the list are ordered by increasing distance from the origin
	)))		
}

/************************** Manual Mode Constraints **************************/

// returns true only if the EGAS validates the streets composing the BP
pred validatedByEGAS[bp: BikePath] {
	bp in ManuallyInsertedBikePath and bp.infoInserted = True and bp.validatedByEGAS = True and bp.published = False
}

// returns true if a path can be validated by the EGAS. A path can be validated by the EGAS if it is formed by adjacent streets and has no repeated streets in it.
pred validableByEGAS[bp: BikePath] {
	bp in ManuallyInsertedBikePath and bp.validatedByEGAS = False and bp.infoInserted = True and bp.published = False and all sn: StreetNode | (sn.bikePath = bp implies ( 
		(sn.end = False implies sn.nextStreet.street in sn.street.adjacentStreets) and									// a path must be formed by adjacent streets
		(sn.end = False implies sn.street not in sn.^nextStreet.street)											// a path must have no repeated streets in it
	))
}

/*since the only variable field of a streetNode is potholesDetected, a list of StreetNode is unchanged in the next instant if all the fields potholeDetected are unchanged and the BikePath has the same origin (even the nextStreet field is static
so, a different list of street is just a list with a different origin or different potholes)*/
pred streetListUnchanged[bp: BikePath] {
	(all sn: StreetNode | sn.bikePath = bp implies sn.potholesDetected = (sn.potholesDetected)') and bp.origin = (bp.origin)'
}

// if the info manually inserted is correct then, in the next instant, it will be validated by the EGAS, so it cannot be modified anymore
fact EGASValidationConstraint {
	always (all bp: BikePath |  validableByEGAS[bp] implies ((after validatedByEGAS[bp]) and bp.status = (bp.status)' and streetListUnchanged[bp]))
}

// if a user is modifying a wrong path before the EGAS validation, then the unmodifiable fields should be the same over all instants
fact manualModificationConstraint {
	always (all bp: BikePath | infoInsertedManually[bp] implies (bp.published = (bp.published)' and bp.infoInserted = (bp.infoInserted)' and (not  validableByEGAS[bp] implies after bp.validatedByEGAS = False)))
}

/************************** Automated Mode Constraints **************************/

// if a BP is inserted using automated mode user can either correct or confirm the data retrieved, not both. This happens in the next instant and is permanent
fact userValidationConstraint {
	always (all bp: BikePath | ( infoInsertedAutomatically[bp] implies (
		after always ((bp.correctedByUser = True and bp.confirmedByUser = False) or (bp.correctedByUser = False and bp.confirmedByUser = True))
	)))
}

// returns true if the BP is unchanged in the next instant (including the potholes detected, excluding the info regarding the two different concrete sig)
pred bikePathUnchanged[bp: BikePath] {
	bp.origin = (bp.origin)' and bp.origin.*nextStreet.potholesDetected = (bp.origin.*nextStreet.potholesDetected)' and
	bp.status = (bp.status)' and bp.infoInserted = (bp.infoInserted)' and bp.published = (bp.published)'
}

// if a BP is confirmed then it is unchanged
fact BPConfirmationConstraint {
	always  (all bp: BikePath | ((bp.confirmedByUser = False and (bp.confirmedByUser)' = True) implies bikePathUnchanged[bp]))
}

// in automated mode users can only modify the potholes detected or the status, because we assume that the gps retrieves data correctly (the street list is correct)
fact BPCorrectionConstraint {
	always  (all bp: BikePath | ((bp.correctedByUser = False and (bp.correctedByUser)' = True) implies (
		bp.origin = (bp.origin)' and
		bp.infoInserted = (bp.infoInserted)'and 
		bp.published = (bp.published)' and (
			bp.status != (bp.status)' or												// status modifiied
			bp.origin.*nextStreet.potholesDetected != (bp.origin.*nextStreet.potholesDetected)')		// potholes modifiied
	)))
}

/************************** Post-Insertion Constraints **************************/

//returns true if the BP has been corrected by a user in automated mode
pred correctedByUser[bp: BikePath] {
	bp in AutomaticallyInsertedBikePath and bp.infoInserted = True and bp.confirmedByUser = False and bp.correctedByUser = True and bp.published = False
}

//returns true if the BP has been confirmed by a user in automated mode
pred confirmedByUser[bp: BikePath] {
	bp in AutomaticallyInsertedBikePath and bp.infoInserted = True and bp.confirmedByUser = True and bp.correctedByUser = False and bp.published = False
}

//returns true if the insertion is completed
pred insertionCompleted[bp: BikePath] {
	validatedByEGAS[bp] or correctedByUser[bp] or confirmedByUser[bp]
}

// once the insertion is completed, the info cannot be modified anymore (it can only be published). 
fact insertionFinalizedConstraint {
	always (all bp: BikePath | (insertionCompleted[bp] implies (
		bp.origin = (bp.origin)' and bp.origin.*nextStreet.potholesDetected = (bp.origin.*nextStreet.potholesDetected)' and
		bp.status = (bp.status)' and bp.infoInserted = (bp.infoInserted)'and
		(bp in ManuallyInsertedBikePath implies bp.validatedByEGAS = (bp.validatedByEGAS)') and
		(bp in AutomaticallyInsertedBikePath implies (bp.confirmedByUser = (bp.confirmedByUser)' and bp.correctedByUser = (bp.correctedByUser)'))
	)))
}

//once the BP is published it cannot be made private again (like the fact above but now also the field "published" is immutable)
fact publicationFinalizedConstraint {
	always (all bp: BikePath | (bp.published = True implies (bp.published = (bp.published)' and
		bp.origin = (bp.origin)' and bp.origin.*nextStreet.potholesDetected = (bp.origin.*nextStreet.potholesDetected)' and
		bp.status = (bp.status)' and bp.infoInserted = (bp.infoInserted)'and
		(bp in ManuallyInsertedBikePath implies bp.validatedByEGAS = (bp.validatedByEGAS)') and
		(bp in AutomaticallyInsertedBikePath implies (bp.confirmedByUser = (bp.confirmedByUser)' and bp.correctedByUser = (bp.correctedByUser)'))
	)))
}

/*NOTE: with these constraints a BP could either be eventually published or never published*/

/************************** Predicates to show different worlds **************************/

pred showCreationToPublicationOfAnAutomaticallyInsertedBikePathWithoutCorrection{
	#BikePath = 0; 
	#AutomaticallyInsertedBikePath = 1 and #BikePath = 1;
	#StreetNode = 3 and #PotholeNode = 1;
	all bp: BikePath | bp.confirmedByUser = True;
	all bp: BikePath | bp.published = False;
	all bp: BikePath | bp.published = True 
}

run showCreationToPublicationOfAnAutomaticallyInsertedBikePathWithoutCorrection for 3 but 4 Street, 7 steps
	
pred showCreationToPublicationOfAnAutomaticallyInsertedBikePathWithCorrection{
	#BikePath = 0; 
	#AutomaticallyInsertedBikePath = 1 and #BikePath = 1;  
	#StreetNode = 2 and #PotholeNode = 1; 
	all bp: BikePath | bp.correctedByUser = True  and #PotholeNode = 3; 
	all bp: BikePath | bp.published = False; 
	all bp: BikePath | bp.published = False; 
	all bp: BikePath | bp.published = True
}

run showCreationToPublicationOfAnAutomaticallyInsertedBikePathWithCorrection for 3 but 4 Street, 7 steps

pred showCreationToPublicationOfAManuallyInsertedBikePath{
	#BikePath = 0 and #Street = 5;
	#ManuallyInsertedBikePath = 1 and #BikePath = 1;
	#StreetNode = 3 and #PotholeNode = 0 and all bp: BikePath | not validableByEGAS[bp]; 
	#StreetNode = 3 and all bp: BikePath | validableByEGAS[bp]; 
	all bp: BikePath | validatedByEGAS[bp]; 
	all bp: BikePath | bp.published = True
}

run showCreationToPublicationOfAManuallyInsertedBikePath for 3 but 6 Street, 4 StreetNode, 6 steps

/************************** Assertions **************************/

// checks that the publications can happen only if all information of a BP has been correctly entered and validated
assert bikePathsMustBeCompleteBeforePublished {
	always (all bp: BikePath | bp.published = True implies once insertionCompleted[bp])
}

check bikePathsMustBeCompleteBeforePublished for 5

// checks if, when a path is inserted in automated mode and the users confirms it, then the structure of the path never changes anymore
assert bikePathImmutableAfterConfirmation {
	always (all bp: BikePath | (infoInsertedAutomatically[bp] and after confirmedByUser[bp]) implies streetListUnchanged[bp])
}

check bikePathImmutableAfterConfirmation for 5 but 1 BikePath

// checks if a public path is correct in terms of "street list consistency"
assert publicPathWithCorrectStreetList {
	always (all bp: BikePath | bp.published = True implies (all sn: StreetNode | (sn.bikePath = bp and sn.end = False) implies (sn.nextStreet.street in sn.street.adjacentStreets and sn.street not in sn.^nextStreet.street)))
}

check publicPathWithCorrectStreetList for 5 but 1 BikePath, 6 steps

// checks the fact that the street list is always constant in time when the BP is inserted through automated mode (the only thing varying are the potholes or the status)
assert usersCannotModifyStreetListInAutomaticallyInsertedBikePaths {
	always (all bp: AutomaticallyInsertedBikePath | infoInsertedAutomatically[bp] implies after always bp.origin = (bp.origin)')
}

check usersCannotModifyStreetListInAutomaticallyInsertedBikePaths for 5 but 1 BikePath

// checks that if a user has inserted an invalid BP in manual mode and so the EGAS did not confirm it, then the user must have modified it before validation by the EGAS
assert userMustModifyPathNotConfirmedByEGAS {
	always (all bp: ManuallyInsertedBikePath | (infoInsertedManually[bp] and after (bp.validatedByEGAS = False) and eventually (bp.validatedByEGAS = True)) implies
	 eventually (bp.origin != (bp.origin)' or bp.origin.*nextStreet.potholesDetected != (bp.origin.*nextStreet.potholesDetected)'))
}

check userMustModifyPathNotConfirmedByEGAS for 5 but 1 BikePath, 6 steps

// checks that, when confirming an AutomaticallyInsertedBikePath, the path structure and the status are unchanged in the future 
assert usersConfirmationShouldNotModifyBikePath {
	always (all bp: AutomaticallyInsertedBikePath | (bp.confirmedByUser = False and (bp.confirmedByUser)' = True) implies after always (streetListUnchanged[bp] and bp.status = (bp.status)'))
} 

check usersConfirmationShouldNotModifyBikePath for 5 but 1 BikePath, 8 steps

// checks that publication can happen only after at least three instants after the creation of a BP (creation -> insertion -> validation (insertion finalized) -> publication)
assert publicationOnlyAfterThreeInstants {
	always (not (some bp: BikePath | bp.published = True and (before newlyCreatedBikePath[bp] or before before newlyCreatedBikePath[bp] )))
}

check publicationOnlyAfterThreeInstants for 5

// checks that publication can never happen before the finalization of the insertion
assert publicationOnlyAfterFinalizationOfInsertion {
	always (not (some bp: BikePath | bp.published = True and historically not insertionCompleted[bp]))
}

check publicationOnlyAfterFinalizationOfInsertion for 5

// checks that after the insertion is finalized the BP will never go back in a state in which is either not validated by the EGAS (manual mode) or has not been confirmed/corrected by the user (automated mode)
assert afterInsertionFinalizedCannotGoBackInInsertionState {
	always (all bp: BikePath | insertionCompleted[bp] implies after always not infoInserted[bp])
}

check afterInsertionFinalizedCannotGoBackInInsertionState for 5

// checks that states related only to ManuallyInsertedBikePath are never connected to the ones related only to AutomaticallyInsertedBikePath
assert differentBikePathStatesCoherence {
	always ((not (some bp: ManuallyInsertedBikePath | insertionCompleted[bp] and after (correctedByUser[bp] or confirmedByUser[bp]))) and
		    (not (some bp: AutomaticallyInsertedBikePath | insertionCompleted[bp] and after validatedByEGAS[bp]))
	)
}

check differentBikePathStatesCoherence for 5
