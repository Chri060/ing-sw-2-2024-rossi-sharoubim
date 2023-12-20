//SIGNATURES

sig Username{}
sig Email{}
sig Telephone{}

abstract sig User {
	username : disj one Username,
	email : disj one Email,
	telephone : disj one Telephone
}

sig Educator extends User{}

sig Student extends User{}

sig Battle {
	registrationDate : one Int,
	submissionDate : one Int,
	creator : Educator,
	tournament : one Tournament,
	about : one CodeKata
} {registrationDate > 0 and 
	submissionDate > registrationDate}

sig Group {
	students : some Student,
	battle : one Battle,	
	points : one Int
} {points > 0}

sig Tournament {
	registrationDate : Int,
	owner : one Educator,
	managedBy : set Educator,
	partecipants : set Student
} {owner not in managedBy}

sig Ranking {
	student : one Student,
	tournament : one Tournament,
	points : one Int
} {points >= 0}

sig CodeKata {
}

//FUNCTIONS

fun getStudentGroupsPerTournament [s : Student, t : Tournament] : Group {
	{g : Group | s in g.students and t = (g.battle).tournament}
}

fun getStudentRankPerTournament[s : Student, t : Tournament] : Int {
	{i : sum[getStudentGroupsPerTournament[s, t].points]}
}


// FACTS

//Every battle in a tournament is made by an educator that created it or manages it
fact onlyAutorazedCanCreateBattles {
	all b : Battle | b.creator in ((b.tournament).owner + (b.tournament).managedBy)
}

//Only students that partecipate in a tournament have a rank in it
fact onlyPartecipantsRanked {
	all r : Ranking | r.student in (r.tournament).partecipants
}

//Every partecipant in tournament gets a ranking in it
fact everyPartecipantIsRanked {
	all t : Tournament | all s : t.partecipants |
		one r : Ranking | r.student = s and r.tournament = t
}

//Only partecipants in a tournament can also join its battles
fact onlyEnrolledCanBattle {
	all g : Group | all s : g.students | s in ((g.battle).tournament).partecipants
}

//No group referred to the same battle can contain the same student
fact noOverlappingStudents {
	all disj g1, g2 : Group | g1.battle = g2.battle => no (g1.students & g2.students)}

//Ranking of a tournament are given by the sum of the points in each battle 
fact rankingIsPointsSum {
	all r : Ranking | r.points = getStudentRankPerTournament[r.student, r.tournament]
}

//Every student subscribed to a tournament that haven't partecipated in any battle has a ranking of 0
assert noBattleNoPoints {
	all r : Ranking | no getStudentGroupsPerTournament[r.student, r.tournament] implies r.points = 0
}

run {
	#Battle > 0
	#Group > 2
	some g : Group | #g.students > 1
} for 30
