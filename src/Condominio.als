sig Veiculo {}

abstract sig Morador {
	veiculos: set Veiculo	
}

sig MoradorTitular extends Morador {
	dependentes: set MoradorDependente
}

sig MoradorDependente extends Morador {}

sig Condominio {
	moradores: set Morador
}

fact exatamenteUmCondominio {
	# Condominio = 1
}

fact todoMoradorPertenceAoCondominio {
	all m: Morador | one m.~moradores
}

fact moradorDependenteDeUmTitular {
	all d: MoradorDependente | # d.~dependentes = 1
}

fact veiculoTemPeloMenosUmMorador {
	all v: Veiculo | some v.~veiculos
}

fact limiteVeiculosTemporarios {
	all m: Morador | # m.veiculos <= 2
}

fact moradoresTitularesVeiculosDiferentes {
	all t1: MoradorTitular | all t2: MoradorTitular | t1 != t2 implies t1.veiculos != t2.veiculos
}

fact mesmoVeiculos {
	all t: MoradorTitular | all d: t.dependentes | t.veiculos = d.veiculos
} 

pred show [] {}

run show for 10
