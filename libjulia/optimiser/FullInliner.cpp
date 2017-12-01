/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Optimiser component that performs function inlining for arbitrary functions.
 */

#include <libjulia/optimiser/FullInliner.h>

#include <libjulia/optimiser/ASTCopier.h>
#include <libjulia/optimiser/ASTWalker.h>

#include <libsolidity/inlineasm/AsmData.h>

#include <libsolidity/interface/Exceptions.h>

#include <libdevcore/CommonData.h>

#include <boost/range/adaptor/reversed.hpp>

using namespace std;
using namespace dev;
using namespace dev::julia;
using namespace dev::solidity;


string NameDispenser::newName(string const& _prefix)
{
	string name = _prefix;
	size_t suffix = 0;
	while (name.empty() || m_usedNames.count(name))
	{
		suffix++;
		name = _prefix + "_" + std::to_string(suffix);
	}
	m_usedNames.insert(name);
	return name;
}

FullInliner::FullInliner(Block& _block)
{
	m_astCopy = make_shared<Block>(boost::get<Block>(ASTCopier()(_block)));
	m_nameCollector = make_shared<NameCollector>();
	(*m_nameCollector)(*m_astCopy);
	m_nameDispenser.m_usedNames = m_nameCollector->names();
}

vector<Statement> FullInliner::operator()(FunctionalInstruction& _instr)
{
	return visitVector(_instr.arguments, {}, {});
}

vector<Statement> FullInliner::operator()(FunctionCall&)
{
	solAssert(false, "Should have called tryInline().");
	return {};
}

vector<Statement> FullInliner::operator()(Assignment& _assignment)
{
	solAssert(_assignment.value, "");
	solUnimplementedAssert(_assignment.variableNames.size() == 1, "");
	return tryInline(*_assignment.value);
}

vector<Statement> FullInliner::operator()(VariableDeclaration& _varDecl)
{
	solUnimplementedAssert(_varDecl.variables.size() == 1, "");
	return tryInline(*_varDecl.value);
}

vector<Statement> FullInliner::operator()(If& _if)
{
	// Do not visit the condition because we cannot inline there.
	(*this)(_if.body);
	return {};
}

vector<Statement> FullInliner::operator()(Switch& _switch)
{
	// Do not visit the expression because we cannot inline there.
	for (auto& cse: _switch.cases)
		(*this)(cse.body);
	return {};
}

vector<Statement> FullInliner::operator()(FunctionDefinition& _funDef)
{
	m_functionScopes.insert(_funDef.name);
	(*this)(_funDef.body);
	solAssert(m_functionScopes.count(_funDef.name), "");
	m_functionScopes.erase(_funDef.name);
	return {};
}

vector<Statement> FullInliner::operator()(ForLoop& _loop)
{
	(*this)(_loop.pre);
	// Do not visit the condition because we cannot inline there.
	(*this)(_loop.post);
	(*this)(_loop.body);
	return {};
}

vector<Statement> FullInliner::operator()(Block& _block)
{
	// TODO: optimize the number of moves here.
	for (size_t i = 0; i < _block.statements.size(); ++i)
	{
		vector<Statement> data = tryInline(_block.statements.at(i));
		if (!data.empty())
		{
			size_t length = data.size();
			_block.statements.insert(
				_block.statements.begin() + i,
				std::make_move_iterator(data.begin()),
				std::make_move_iterator(data.end())
			);
			i += length;
		}
	}
	return {};
}

vector<Statement> FullInliner::visitVector(
	vector<Statement>& _statements,
	vector<string> const& _nameHints,
	vector<string> const& _types,
	bool _moveToFront
)
{
	// If one of the elements moves parts to the front, all other elements right of it
	// also have to be moved to the front to keep the order of evaluation.
	vector<Statement> prefix;
	for (size_t i = 0; i < _statements.size(); ++i)
	{
		auto& arg = _statements[i];
		// TODO optimize vector operations, check that it actually moves
		vector<Statement> argPrefix = tryInline(arg);
		if (!argPrefix.empty())
		{
			_moveToFront = true;
			// We go through the arguments left to right, so we have to invert
			// the prefixes.
			prefix = std::move(argPrefix) + std::move(prefix);
		}
		else if (_moveToFront)
		{
			auto location = locationOf(arg);
			string var = newName(i < _nameHints.size() ? _nameHints[i] : "");
			prefix.emplace(prefix.begin(), VariableDeclaration{
				location,
				{{TypedName{location, var, i < _types.size() ? _types[i] : ""}}},
				make_shared<Statement>(std::move(arg))
			});
			arg = Identifier{location, var};
		}
	}
	return prefix;
}

vector<Statement> FullInliner::tryInline(Statement& _statement)
{
	if (_statement.type() != typeid(FunctionCall))
		return boost::apply_visitor(*this, _statement);

	FunctionCall& funCall = boost::get<FunctionCall>(_statement);

	// TODO: Insert good heuristic here.
	bool doInline = !m_functionScopes.count(funCall.functionName.name);

	FunctionDefinition const& fun = *m_nameCollector->functions().at(funCall.functionName.name);
	solUnimplementedAssert(fun.returns.size() == 1, "");

	vector<Statement> prefixStatements;
	{
		vector<string> argNames;
		vector<string> argTypes;
		for (auto const& arg: fun.arguments)
		{
			argNames.push_back(fun.name + "_" + arg.name);
			argTypes.push_back(arg.type);
		}
		prefixStatements = visitVector(funCall.arguments, argNames, argTypes, doInline);
	}

	if (doInline)
	{
		map<string, string> variableReplacements;
		for (size_t i = 0; i < funCall.arguments.size(); ++i)
			variableReplacements[fun.arguments[i].name] = boost::get<Identifier>(funCall.arguments[i]).name;
		variableReplacements[fun.returns[0].name] = newName(fun.name + "_" + fun.returns[0].name);

		prefixStatements.emplace_back(VariableDeclaration{
			funCall.location,
			{{funCall.location, variableReplacements[fun.returns[0].name], fun.returns[0].type}},
			{}
		});
		prefixStatements.emplace_back(BodyCopier(m_nameDispenser, fun.name + "_", variableReplacements)(fun.body));
		// TODO this may lead to infinite recursion.
		// TODO this is does duplicate work, because it inlines after having copied
		tryInline(prefixStatements.back());
		_statement = Identifier{funCall.location, variableReplacements[fun.returns[0].name]};
	}
	return prefixStatements;
}

string FullInliner::newName(string const& _prefix)
{
	return m_nameDispenser.newName(_prefix);
}

Statement BodyCopier::operator()(VariableDeclaration const& _varDecl)
{
	// TODO: add function name
	for (auto const& var: _varDecl.variables)
		m_variableReplacements[var.name] = m_nameDispenser.newName(m_varNamePrefix + var.name);
	return ASTCopier::operator()(_varDecl);
}

Statement BodyCopier::operator()(FunctionDefinition const& _funDef)
{
	solAssert(false, "Function hoisting has to be done before function inlining.");
	return _funDef;
}

string BodyCopier::translateIdentifier(string const& _name)
{
	if (m_variableReplacements.count(_name))
		return m_variableReplacements.at(_name);
	else
		return _name;
}
