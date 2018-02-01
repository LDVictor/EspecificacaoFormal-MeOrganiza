-- Especificação Formal do Project Omega em Alloy

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

module ProjectOmega 

-- Assinaturas

one sig ProjectOmega {
	user: one User
}

one sig User {
	name: one Username,
	email: one Email,
	password: one Password,
	cellphone: one Cellphone,
	minimum_score: one MinimumScore,
	semesters: set Semester
}

one sig Username {}
one sig Email {}
one sig Password {}
one sig Cellphone {}
one sig MinimumScore {}

sig Semester {
	alias: one Alias,
	courses: set Course
}

sig Alias {}

sig Course {
	name: one Coursename,
	description: one Description,
	grades: set Grade,
	abssences_allowed: one AbsAllowed,
	abssences_committed: one AbsCommitted,
	tasks: set Task,
	aditionalInfos: set AditionalInfo
}

sig Coursename {}

sig AditionalInfo {
--	name_info: one Infoname,
--	info: one Information
}

--sig Infoname {}
sig Description {}
--sig Information {}
sig Grade {}

sig AbsAllowed {
--	abssence: set Abssence
}

sig AbsCommitted {
--	abssence: set Abssence
}

--sig Abssence {
--	time: one Datetime,
--	reason: one Reason
--}

--sig Reason {}
--sig Datetime {}

sig Task {
	name: one Taskname,
	description: one Description,
	start: one TStart,
	close: one TClose,
	pomodoros: set Pomodoro
}

sig Taskname {}
sig TStart {}
sig TClose {}

sig Pomodoro {
	description: one PomodoroInfo,
	start: one PStart,
	close: one PClose
}

sig PStart {}
sig PClose {}
sig PomodoroInfo{}

-- Fatos e Restrições

fact UserConstraints {

-- O usuário pode ter no máximo 3 semestres
	all u : User | #(u.semesters) < 4

-- Todo semestre deve estar relacionado ao usuário
	all s : Semester | one u : User | s in u.semesters
}

fact SemesterConstraints {

-- Todo semestre pode ter no mínimo 1 curso e no máximo 10 cursos
	all s : Semester | #(s.courses) > 0 
	all s : Semester | #(s.courses) < 2

-- Todo curso deve estar relacionado a apenas um semestre
	all c : Course | one s : Semester | c in s.courses
}

fact CourseConstraints {

-- Todo coursename deve estar relacionado a apenas um curso
	all n : Coursename | lone c : Course | n in c.name

-- Toda descrição deve estar relacionada a apenas um curso
	all d : Description | lone c : Course | d in c.description

-- Toda nota deve estar relacionada a apenas um curso
	all g : Grade | lone c : Course | g in c.grades

-- Cada curso deve ter exatamente 3 notas
	all c : Course | #(c.grades) = 3

-- Toda falta deve estar relacionada a apenas um curso
	all a : AbsAllowed | lone c : Course | a in c.abssences_allowed
	all a : AbsCommitted | lone c : Course | a in c.abssences_committed

-- O número de faltas não pode ser igual às faltas permitidas
--	all c : Course | #(c.abssences_committed) < #(c.abssences_allowed)

-- Toda task deve estar relacionada a apenas um curso
	all t : Task | lone c : Course | t in c.tasks

-- Cada curso pode ter no máximo 3 tasks
	all c : Course | #(c.tasks) < 4

-- Cada informação adicional deve estar relacionada a apenas um curso
	all a : AditionalInfo | lone c : Course | a in c.aditionalInfos

-- Cada curso pode ter no máximo 2 informações adicionais
	all c : Course | #(c.aditionalInfos) < 3
}

-- Show
pred show[]{ }
run show for 20

	




