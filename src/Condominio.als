module Condominio

-- VEICULOS
abstract sig Veiculo {}

sig VeiculoGrande extends Veiculo {}
sig VeiculoMedio extends Veiculo {}
sig VeiculoPequeno extends Veiculo {}

-- VAGAS

abstract sig Vaga {
	veiculo: lone Veiculo
}

sig VagaNormal extends Vaga {}
sig VagaPreferencial extends Vaga {}

-- MORADOR
abstract sig Morador {
	veiculos: set Veiculo	
}

sig MoradorTitular extends Morador {
	dependentes: set MoradorDependente
}

sig MoradorDependente extends Morador {}

-- CONDOMINIO
sig Portao {}

one sig Condominio {
	moradores: set Morador,
	vagas: set Vaga,
	portao: one Portao
}

-- FACTS
fact todoMoradorPertenceAoCondominio {
	all m: Morador | one m.condominio
}

fact todaVagaPertenceAoCondominio {
	all v: Vaga | one v.condominio
}

fact moradorDependenteDeUmTitular {
	all d: MoradorDependente | one d.titular
}

fact veiculoTemPeloMenosUmMorador {
	all v: Veiculo | one m: Morador | m in v.moradores
}

fact limiteVeiculosTemporarios {
	all t: MoradorTitular | # t.veiculosDoMorador <= 2
}

fact moradoresTitularesVeiculosDiferentes {
	all t1: MoradorTitular | all t2: MoradorTitular | t1 != t2 implies t1.veiculos != t2.veiculos
}

fact veiculoDeDependenteTemRegistrador {
	all v: Veiculo | (v.~veiculos in MoradorDependente) => one v.moradores.titular
}

fact umaVagaPorVeiculo {
	all v: Veiculo | lone v.vaga
}

fact minimoDeVagasPreferenciais {
	not (# VagaPreferencial < div[# Vaga, 10])
}

fact minimoDeVagasNormais {
	not (# VagaNormal < div[# Vaga, 10])
}

fact peloMenosUmaVagaPreferencial {
	# Vaga > 1 => (# VagaPreferencial > 0)
}

fact maisVagasNormaisDoQuePreferenciais {
	# VagaNormal > # VagaPreferencial
}

-- FUNS
fun veiculosDoMorador (m: Morador): set Veiculo {
	(m.veiculos + m.dependentes.veiculos)
}

fun proprietario (v: Veiculo): Morador {
	v.~veiculos
}

fun registrador (v: Veiculo): MoradorTitular {
	v.proprietario.titular + v.proprietario - MoradorDependente
}

fun condominio (m: Morador) : set Condominio {
	m.~moradores
}

fun condominio (v: Vaga) : set Condominio {
	v.~vagas
}

fun titular (d: MoradorDependente) : set MoradorTitular {
	d.~dependentes
}

fun moradores (v: Veiculo) : set Morador {
	v.~veiculos
}

fun vaga (v: Veiculo) : set Vaga {
	v.~veiculo
}

-- ASSERTS
assert veiculoTemDonoNoCondominio {
	all v: Veiculo | v.proprietario in Condominio.moradores
}

assert maximoDoisVeiculosPorMorador {
	all m: Morador | # veiculosDoMorador[m] <= 2
}

assert totalDeVeiculosEhValido {
	(# Veiculo) <= mul[# MoradorTitular, 2]
}

assert registradorCorreto {
	all v: Veiculo | v.proprietario in MoradorDependente => v.proprietario in v.proprietario.titular.dependentes
}

-- PREDS
pred temVeiculoRegistrado(m: Morador) {
	# m.veiculosDoMorador > 0
}

pred podeRegistrarVeiculo(m: Morador) {
	# m.veiculosDoMorador < 2
}

pred ehProprietario(m: Morador, v: Veiculo) {
	m = v.proprietario
}

pred show [] {}

run show for 10
check registradorCorreto for 10
