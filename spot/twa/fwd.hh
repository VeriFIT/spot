// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <memory>

namespace spot
{
  class bdd_dict;
  /// \ingroup twa_essentials
  /// \brief Shared pointer to a bdd_dict.
  typedef std::shared_ptr<bdd_dict> bdd_dict_ptr;

  class twa;
  /// \ingroup twa_essentials
  /// \brief Shared pointer to a mutable twa.
  typedef std::shared_ptr<twa> twa_ptr;
  /// \ingroup twa_essentials
  /// \brief Shared pointer to a const twa.
  typedef std::shared_ptr<const twa> const_twa_ptr;

  class twa_graph;
  /// \ingroup twa_representation
  /// \brief Shared pointer to a const twa_graph.
  typedef std::shared_ptr<const twa_graph> const_twa_graph_ptr;
  /// \ingroup twa_representation
  /// \brief Shared pointer to a mutable twa_graph.
  typedef std::shared_ptr<twa_graph> twa_graph_ptr;

  class twa_product;
  /// \ingroup twa_on_the_fly_algorithms
  /// \brief Shared pointer to a const twa_product.
  typedef std::shared_ptr<const twa_product> const_twa_product_ptr;
  /// \ingroup twa_on_the_fly_algorithms
  /// \brief Shared pointer to a mutable twa_product.
  typedef std::shared_ptr<twa_product> twa_product_ptr;

  struct twa_word;
  /// \ingroup twa_essentials
  /// \brief Shared pointer to a const twa_word.
  typedef std::shared_ptr<const twa_word> const_twa_word_ptr;
  /// \ingroup twa_essentials
  /// \brief Shared pointer to a mutable twa_word.
  typedef std::shared_ptr<twa_word> twa_word_ptr;
}
