/**
Tema 5 - Salão Dona Inês

O salão de dona Inês B. oferece serviços de cabeleireiro (corte, escova, hidratação), manicure e maquiagem. 
O salão conta com três cabeleireiros, uma manicure e um maquiador. 
Cada cabeleireiro atende a cinco clientes por dia, enquanto a manicure e o maquiador atendem a três. 
Os clientes que não conseguirem vagas no dia são alocados para as vagas do dia seguinte. 
O salão também oferece pacotes promocionais e não acumulativos. 
A promoção Panterona oferece hidratação grátis para os clientes que usarem dois serviços do salão. 
A promoção Graças à Deus oferece maquiagem grátis para quem optar pelo combo formado por três serviços.

Integrantes: Gabriel Cintra, Gabriel Guimarães, Francisco Junior, Rafaela Lacerda,  Marcelo Catalão e Jeferson Ferreira
Cliente: Hadrizia

OBSERVAÇÕES:
- Usamos recursão no projeto. Logo, deve-se ir em "Options -> Recursion Depth: 3".
- Os checks estão comentados, para testá-los, basta remover "--", assim como o init[].
**/

module SalaoDonaInes
open util/ordering[Dia]

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- ASSINATURAS
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

sig Dia{}

one sig Salao {
	clientes: set Cliente -> Dia,
	funcionarios : set Funcionario
}

sig Cliente {
	servicos: set Servico -> Dia,
	promocao: Promocao -> Dia
}

abstract sig Funcionario {
	atendimentos: set Cliente -> Dia
}

sig Cabeleireiro extends Funcionario {}
sig Manicure extends Funcionario {}
sig Maquiador extends Funcionario {}

abstract sig Servico {}
abstract sig ServicoCabelo extends Servico {}

one sig Unha extends Servico {}
one sig Maquiagem extends Servico {}
one sig Corte extends ServicoCabelo {}
one sig Hidratacao extends ServicoCabelo {}
one sig Alisamento extends ServicoCabelo {}

abstract sig Promocao { 
	servicoPromocional: one Servico 
}
one sig Panterona extends Promocao {}
one sig GracasADeus extends Promocao {}

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- FATOS
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

fact Traces {
	-- Instâncias que mudam ao decorrer do tempo
	init[first]
	all dia: Dia-last | let dia' = dia.next |
	some cliente: Cliente, serv: Servico |
	(addCliente[cliente, serv, dia, dia'] or delCliente[cliente, dia, dia']) and
	(addServico[serv, cliente, dia, dia'] or delServico[serv, cliente, dia, dia'])
}

fact Funcionarios {
	-- Todo funcionario trabalha no salão
	all func: Funcionario | func in getFuncionarios[]

	-- Quantidade de funcionários no salão
	#Cabeleireiro = 3
	#Manicure = 1
	#Maquiador = 1

	-- Quantidade máxima de clientes atendidos num dia
	all func: Cabeleireiro, dia: Dia | #getAtendimentos[func, dia] <= 5
	all func: Funcionario - Cabeleireiro, dia: Dia | #getAtendimentos[func, dia] <= 3

	-- Cabeleireiros não compartilham o mesmo cliente
	all cab1: Cabeleireiro, cab2: Cabeleireiro - cab1, dia: Dia | #(getAtendimentos[cab1, dia] & getAtendimentos[cab2, dia]) = 0
}

fact Cliente {
	-- Se um cliente está sendo atendido, então ele é um cliente do salão
	all cliente: Cliente, dia: Dia | (cliente in getAtendimentos[Funcionario, dia] ) => (cliente in getClientes[dia])

	-- Se um cliente não tem serviços, então ele não está sendo atendido (e vice-versa)
	all cliente: Cliente, dia: Dia | (#getServicos[cliente, dia] = 0) <=> ((cliente !in getAtendimentos[Funcionario, dia] ) and (cliente !in getClientes[dia]))

	-- Se um cliente contratou um serviço, então um funcionário que realiza esse serviço o atende (e vice-versa)
	all cliente: Cliente, dia: Dia | ((Maquiagem in getServicos[cliente, dia]) or (GracasADeus in cliente.promocao.dia)) <=> (cliente in getAtendimentos[Maquiador, dia] )
	all cliente: Cliente, dia: Dia | (Unha in getServicos[cliente, dia]) <=> (cliente in getAtendimentos[Manicure, dia] )
	all cliente: Cliente, dia: Dia | ((Hidratacao in getServicos[cliente, dia]) or (Corte in getServicos[cliente, dia]) or 
													(Alisamento in getServicos[cliente, dia]) or (Panterona in cliente.promocao.dia)) <=> 
													(cliente in getAtendimentos[Cabeleireiro, dia])
}

fact Promocao {
	-- Determina os serviços promocionais das duas promoções
	Panterona.servicoPromocional = Hidratacao and GracasADeus.servicoPromocional = Maquiagem

	-- Verifica se atente aos requisitos da promoção Panterona. Se sim, adiciona a promoção e aloca um funcionário.
	all cliente: Cliente, dia: Dia | !podeGanharPanterona[cliente, dia] => (Panterona !in getPromocao[cliente, dia])
	all cliente: Cliente, dia: Dia | podeGanharPanterona[cliente, dia] => ((Panterona in getPromocao[cliente, dia]) and (cliente in getAtendimentos[Cabeleireiro, dia]))

	-- Verifica se atente aos requisitos da promoção Graças a Deus. Se sim, adiciona a promoção e aloca um funcionário.
	all cliente: Cliente, dia: Dia | !podeGanharGracasADeus[cliente, dia] => (GracasADeus !in getPromocao[cliente, dia])
	all cliente: Cliente, dia: Dia | podeGanharGracasADeus[cliente, dia] =>  ((GracasADeus in getPromocao[cliente, dia]) and (cliente in getAtendimentos[Maquiador, dia]))
}

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- PREDICADOS
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

pred init[dia: Dia]{
	/*
	* Define o estado inicial do modelo
	* Se quiser que o salão comece sem clientes, basta descomentar a linha.
	*/

	--#(Salao.clientes.dia) = 0
}


pred addCliente[cliente: Cliente, serv: Servico, dia, dia': Dia] {
	-- Checa se precisa realocar o horário caso o salão esteja cheio
	(salaoEstaCheio[dia]) => (realocaHorarios[dia, dia'] and addCliente[cliente, serv, dia, dia']) else
	((cliente !in getClientes[dia]) => (getClientes[dia'] = (getClientes[dia]) + cliente) and addServico[serv, cliente, dia, dia'])
}

pred delCliente[cliente: Cliente, dia, dia': Dia] {
	-- Remove o cliente dos clientes atendidos pelo salão
	(cliente in getClientes[dia])
	(getClientes[dia'] = (getClientes[dia]) - cliente)
	
	-- Remove todos os serviços contratados pelo cliente
	all serv: Servico | delServico[serv, cliente, dia, dia']
}

pred addServico[serv: Servico, cliente: Cliente, dia, dia': Dia] {
	-- Adiciona serviço a um cliente
	(serv !in getServicos[cliente, dia])
	(getServicos[cliente, dia'] = (getServicos[cliente, dia]) + serv)
}

pred delServico[serv: Servico, cliente: Cliente, dia, dia': Dia] {
	-- Adiciona serviço a um cliente
	(serv in getServicos[cliente, dia])
	(getServicos[cliente, dia'] = (getServicos[cliente, dia]) - serv)
}

pred podeGanharPanterona[cliente: Cliente, dia: Dia] {
	-- Verifica se o pedido atende as especificaçoes da Panterona (2 Serviços no dia que não seja Hidratação)
	(#getServicos[cliente, dia] = 2) and (Hidratacao !in getServicos[cliente, dia])
}

pred podeGanharGracasADeus[cliente: Cliente, dia: Dia] {
	-- Verifica se o pedido atende as especificaçoes de Graças a Deus (3 Serviços no dia que não seja Maquiagem)
	(Panterona !in getPromocao[cliente, dia]) and (#getServicos[cliente, dia] = 3) and (Maquiagem !in getServicos[cliente, dia])
}

pred salaoEstaCheio[dia: Dia] {
	-- Verifica se o salão chegou no limite de clientes atendidos
	#(Funcionario.atendimentos) = 21
}

pred realocaHorarios[dia, dia': Dia] {
	-- Realoca o horário do cliente para amanhã
	(dia = dia.next and dia' = dia'.next)
}

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- FUNÇÕES
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

fun getFuncionarios[]: set Funcionario {
	Salao.funcionarios
}

fun getClientes[dia: Dia]: set Cliente {
	Salao.clientes.dia
}

fun getAtendimentos[func: Funcionario, dia: Dia]: set Cliente {
	func.atendimentos.dia
}

fun getServicos[cliente: Cliente, dia: Dia]: set Servico {
	cliente.servicos.dia
}

fun getPromocao[cliente: Cliente, dia: Dia]: lone Promocao {
	cliente.promocao.dia
}

--------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- ASSERTS & CHECKS
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

assert Panterona {
	-- Procura um cliente com dois serviços (exceto Hidratação) que não possui a promoção Panterona
	!some cliente: Cliente, dia: Dia | !((#getServicos[cliente, dia] = 2) and (Hidratacao !in getServicos[cliente, dia])) and (Panterona in getPromocao[cliente, dia])
}

assert GracasADeus {
	-- Procura um cliente com três serviços (exceto Maquiagem) que não possui a promoção Graças a Deus
	!some cliente: Cliente, dia: Dia | !((#getServicos[cliente, dia] = 3) and (Maquiagem !in getServicos[cliente, dia])) and (GracasADeus in getPromocao[cliente, dia])
}

assert ClienteComDuasPromocoes {
	-- Procura um cliente que tenha recebido ambas as promoções (Panterona e Graças a Deus)
	!some cliente: Cliente, dia: Dia | (Panterona in getPromocao[cliente, dia]) and (GracasADeus in getPromocao[cliente, dia])
}

assert ClientePossuiFuncionarioEServicos {
	-- Procura um cliente que possui um serviço e não está sendo atendido por um funcionário que o realize
	!some cliente: Cliente, dia: Dia | (Unha in getServicos[cliente, dia]) and !(cliente in getAtendimentos[Manicure, dia]) 
	!some cliente: Cliente, dia: Dia | (Maquiagem in getServicos[cliente, dia]) and !(cliente in getAtendimentos[Maquiador, dia]) 
	!some cliente: Cliente, dia: Dia | (ServicoCabelo in getServicos[cliente, dia]) and !(cliente in getAtendimentos[Cabeleireiro, dia]) 
}

assert ClienteDoSalaoSemAtendimento {
	-- Procura um cliente que está no salão mas não está sendo atendido
	!some cliente: Cliente, dia: Dia | (cliente in getClientes[dia]) => !(cliente in getAtendimentos[Funcionario, dia])
}

--check Panterona for 20

--check GracasADeus for 20

--check ClienteComDuasPromocoes for 20

--check ClientePossuiFuncionarioEServicos for 20

--check ClienteDoSalaoSemAtendimento for 20

--------------------------------------------------------------------------------------------------------------------------------------------------------------------

pred SemanaDeTrabalho[] {}
run SemanaDeTrabalho for 7 -- but exactly 22 Cliente
