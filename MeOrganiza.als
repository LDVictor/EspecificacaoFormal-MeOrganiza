-- Especificação Formal do MeOrganiza em Alloy

-- Equipe: 
-- Alice Fernandes Silva
-- Eri Jonhson Oliveira da Silva
-- Gabriel Souto Maracajá
-- Ivyna Rayany Santino Alves
-- José Glauber Braz de Oliveira
-- Mainara Cavalcanti de Farias
-- Pedro Henrique Costa Maia
-- Raquel Rufino Costa da Paz
-- Thalyta Fabrine da Trindade
-- Victor Emanuel Farias da Costa Borges

module MeOrganiza

-- Assinaturas

one sig MeOrganiza {
	user: one User
}

one sig User {
	profile: one Profile,
	semesters: set Semester
}

one sig Profile {
	name: one Username,
	email: one Email,
	password: one Password,
	course: one Course
}

one sig Username {}
one sig Email {}
one sig Password {}
one sig Course {}

sig Semester {
	alias: one Alias,
	subjects: set Subject,
	tasks: set Task,
	isCurrent: one CurrentSemester
}

sig Alias {}
sig CurrentSemester {}

sig Subject {
	name: one Subjectname,
	description: one Description,
	grades: set Grade,
	abssences_allowed: one AbsAllowed,
	abssences_committed: one AbsCommitted,
	aditionalInfos: set AditionalInfo,
	media: one Media
}

sig Subjectname {}

sig Media {
	photos: set Photo,
	documents: set Document
}

sig Photo {}
sig Document {}

sig AditionalInfo {
}

sig Description {}
sig Grade {}

sig AbsAllowed {
}

sig AbsCommitted {
}

sig Task {
	name: one TaskName,
	description: one TaskDescription,
	date: one TaskDate,
	subject: one TaskSubject
}

sig TaskName {}
sig TaskDescription {}
sig TaskDate {}
sig TaskSubject {}

-- Fatos e Restrições

fact UserConstraints {

-- O usuário pode ter no máximo 3 semestres
	all u : User | #(u.semesters) < 4

-- Todo semestre deve estar relacionado ao usuário
	all s : Semester | one u : User | s in u.semesters
}

fact SemesterConstraints {

-- Todo alias deve estar relacionado a apenas um semestre
	all a : Alias | one s : Semester | a in s.alias

-- Todo semestre deve ter um alias
	all s : Semester | #(s.alias) = 1

-- Todo semestre pode ter no mínimo 1 disciplina e no máximo 10 disciplinas
	all s : Semester | #(s.subjects) > 0 
	all s : Semester | #(s.subjects) < 11

-- Toda disciplina deve estar relacionado a apenas um semestre
	all c : Subject | one s : Semester | c in s.subjects

-- Toda task deve estar relacionada a apenas um semestre
	all t : Task | one s : Semester | t in s.tasks

-- Cada semestre pode ter no máximo 3 tasks
	all s : Semester | #(s.tasks) < 4

-- Cada CurrentSemester deve estar relacionado a apenas um semestre
	all c : CurrentSemester | one s : Semester | c in s.isCurrent
}

fact SubjectConstraints {

-- Todo subjectname deve estar relacionado a apenas uma disciplina
	all n : Subjectname | one s : Subject | n in s.name

-- Toda descrição deve estar relacionada a apenas uma disciplina
	all d : Description | one s : Subject | d in s.description

-- Toda nota deve estar relacionada a apenas uma disciplina
	all g : Grade | one s : Subject | g in s.grades

-- Cada disciplina deve ter exatamente 3 notas
	all s : Subject | #(s.grades) = 3

-- Toda falta deve estar relacionada a apenas uma disciplina
	all a : AbsAllowed | one s : Subject | a in s.abssences_allowed
	all a : AbsCommitted | one s : Subject | a in s.abssences_committed

-- Cada informação adicional deve estar relacionada a apenas uma disciplina
	all a : AditionalInfo | one s : Subject | a in s.aditionalInfos

-- Cada disciplina pode ter no máximo 2 informações adicionais
	all s : Subject | #(s.aditionalInfos) < 3

-- Cada mídia deve estar relacionada a apenas uma disciplina
	all m : Media | one s : Subject | m in s.media

-- Cada disciplina tem uma mídia
	all s : Subject | #(s.media) = 1
}

fact MediaConstraints {

-- Cada foto e documento deve estar relacionada a apenas uma mídia
	all p : Photo | one m : Media | p in m.photos
	all d : Document | one m : Media | d in m.documents

-- Cada mídia pode ter no máximo 5 fotos e 3 documentos
	all m : Media | #(m.photos) < 6
	all m : Media | #(m.documents) < 4
}

fact TaskConstraints {

-- Todo taskname deve estar relacionado a apenas um task
	all n : TaskName | one t : Task | n in t.name

-- Toda taskdescription deve estar relacionado a apenas um task
	all d : TaskDescription | one t : Task | d in t.description

-- Toda taskdate deve estar relacionado a apenas um task
	all d : TaskDate | one t : Task | d in t.date

-- Toda tasksubject devem estar relaconados com apenas um task
	all s : TaskSubject | one t : Task | s in t.subject
}

-- Show
pred show[]{ }
run show for 20  but exactly 1 Semester, 1 Subject, 1 Media, 1 Task

	




