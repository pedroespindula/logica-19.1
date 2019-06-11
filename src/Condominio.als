module Cond

sig Veiculo {}

abstract sig Morador {
	veiculos: set Veiculo	
}

sig MoradorTitular extends Morador {
	dependentes: set MoradorDependente
}

sig MoradorDependente extends Morador {}

one sig Condominio {
	moradores: set Morador
}

fact exatamenteUmCondominio {
	# Condominio = 1
}

fact todoMoradorPertenceAoCondominio {
	all m: Morador | one m.~moradores
}

fact moradorDependenteDeUmTitular {
	all d: MoradorDependente | one d.~dependentes
}

fact veiculoTemPeloMenosUmMorador {
	all v: Veiculo | one m: Morador | m in v.~veiculos
}

fact limiteVeiculosTemporarios {
	all t: MoradorTitular | # veiculosDoMorador[t] <= 2
}

fact moradoresTitularesVeiculosDiferentes {
	all t1: MoradorTitular | all t2: MoradorTitular | t1 != t2 implies t1.veiculos != t2.veiculos
}

fact veiculoDeDependenteTemRegistrador {
	all v: Veiculo | (v.~veiculos in MoradorDependente) => one v.~veiculos.~dependentes
}

-- FUNS
fun veiculosDoMorador(m: Morador): set Veiculo {
	(m.veiculos + m.dependentes.veiculos)
}

fun proprietario(v: Veiculo): Morador {
	v.~veiculos
}

fun registradoNoNomeDe(v: Veiculo): MoradorTitular {
	v.~veiculos.~dependentes
}

-- ASSERTS
assert veiculoTemDonoNoCondominio {
	all v: Veiculo | v.~veiculos in Condominio.moradores
}

assert maximoDoisVeiculosPorMorador {
	all m: Morador | # veiculosDoMorador[m] <= 2
}

assert totalDeVeiculosEhValido {
	(# Veiculo) <= mul[# MoradorTitular, 2]
}

-- PREDS
pred temVeiculoRegistrado(m: Morador) {
	# veiculosDoMorador[m] > 0
}

pred podeRegistrarVeiculo(m: Morador) {
	# veiculosDoMorador[m] < 2
}

pred ehDono(m: Morador, v: Veiculo) {
	m = proprietario[v]
}

pred show [] {}

run show for 10
