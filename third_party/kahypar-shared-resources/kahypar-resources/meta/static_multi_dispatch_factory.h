/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2016 Sebastian Schlag <sebastian.schlag@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 ******************************************************************************/

#pragma once

#include <memory>
#include <string>

#include "kahypar-resources/macros.h"
#include "kahypar-resources/meta/function_traits.h"
#include "kahypar-resources/meta/mandatory.h"
#include "kahypar-resources/meta/typelist.h"

namespace kahypar {
namespace meta {
/*!
 * Generalization of StaticDoubleDispatchFactory to support 'true multiple' dispatch.
 * The factory allows to instantiate a concrete Product that uses
 * an arbitrary number of Policies (where each policy can have multiple implementations)
 * at runtime.
 *
 * See static_multi_dispatch_factory_test.cc for an example.
 *
 * \tparam Product The class that should be created
 * \tparam AbstractProduct The base class of Product
 * \tparam Policies A Typelist containing the typelists of all Policies.
 * \tparam CurrentPolicy The Policy that is currently matched.
 *                       This template parameter should not be changed by user code.
 * \tparam MatchedPolicyClasses The typelist containing all types of the policy classes.
 *                              Initially this typelist is empty, since no type is matched yet.
 *                              This template parameter should not be changed by user code.
 */
template <template <typename ...> class Product = MandatoryTemplate,
          typename AbstractProduct = Mandatory,
          typename Policies = Mandatory,
          typename CurrentPolicy = EmptyTypelist,
          typename MatchedPolicyClasses = EmptyTypelist>
class StaticMultiDispatchFactory {
  // ! Return type of concrete product
  using AbstractProductPtr = std::unique_ptr<AbstractProduct>;

 public:
  /*!
   * Helper method to extract a policy class from the OtherPolicyClasses parameter pack.
   * The type of this policy class (i.e.,  PolicyClassToBeMatched) is then matched against
   * the first policy typelist in Policies (i.e., Policies::Head).
   *
   * \tparam ParameterTuple A tuple containing all parameters needed to call Product's constructor
   * \tparam PolicyClassToBeMatched The type of the policy class we are currently trying to match
   * \tparam OtherPolicyClasses The remaining policy classes that are yet to be matched
   */
  template <typename ParameterTuple,
            typename PolicyClassToBeMatched,
            typename ... OtherPolicyClasses>
  static AbstractProduct* createImpl(ParameterTuple&& params, PolicyClassToBeMatched&& policy,
                                     OtherPolicyClasses&& ... policies) {
    return StaticMultiDispatchFactory<Product,
                                      AbstractProduct,
                                      typename Policies::Tail,  // the remaining policies
                                      typename Policies::Head,  // the current policy
                                      MatchedPolicyClasses>::matchPolicy(
      std::forward<ParameterTuple>(params),
      policy,
      policies ...);
  }

  /*!
   * Entry point for factory. Create an instance of Product that implements the policy classes
   * concrete_policy_classes.
   *
   * \tparam ParameterTuple A tuple containing all parameters needed to call Product's constructor
   * \tparam PolicyClasses The concrete policy classes chosen at runtime.
   */
  template <typename ParameterTuple,
            typename ... PolicyClasses>
  static AbstractProduct* create(ParameterTuple&& params,
                                 PolicyClasses&& ... concrete_policy_classes) {
    return StaticMultiDispatchFactory<Product,
                                      AbstractProduct,
                                      Policies,
                                      EmptyTypelist,
                                      MatchedPolicyClasses>::createImpl(
      std::forward<ParameterTuple>(params),
      concrete_policy_classes ...);
  }

  /*!
  * Recursively walk the CurrentPolicy typelist trying to match the type of the current Policy
  * class.
  *
  * \tparam ParameterTuple A tuple containing all parameters needed to call Product's constructor
  * \tparam PolicyClassToBeMatched The type of the policy class we are currently trying to match.
  * \tparam OtherPolicyClasses The remaining policy classes that are yet to be matched.
  */
  template <typename ParameterTuple,
            typename PolicyClassToBeMatched,
            typename ... OtherPolicyClasses>
  static AbstractProduct* matchPolicy(ParameterTuple&& params,
                                      PolicyClassToBeMatched&& current_class,
                                      OtherPolicyClasses&& ... policies) {
    // The type we are now trying to match against PolicyClassToBeMatched.
    using CurrentPolicyClass = typename CurrentPolicy::Head;
    // The remaining types that we need to try in case CurrentPolicyClass does not match.
    using RemainingPolicyClasses = typename CurrentPolicy::Tail;

    if (auto* p1 = dynamic_cast<CurrentPolicyClass*>(&current_class)) {
      // We found the correct type of the current policy class.
      // Add it to the list of matched types and continue matching the class of the
      // next policy.
      using NewMatchedTypes =
        typename concat<MatchedPolicyClasses,
                        Typelist<std::remove_reference_t<CurrentPolicyClass> >
                        >::type;
      // After we found the corresponding type, we have to perform type matching for the
      // remaining policies.
      using RemainingPolicies = Policies;

      return StaticMultiDispatchFactory<Product,
                                        AbstractProduct,
                                        RemainingPolicies,
                                        EmptyTypelist,
                                        NewMatchedTypes>::create(
        std::forward<ParameterTuple>(params),
        policies ...);
    } else {
      // CurrentPolicyClass was not the correct type. Continue matching with the remaining
      // types of the policy.
      return StaticMultiDispatchFactory<Product,
                                        AbstractProduct,
                                        Policies,
                                        RemainingPolicyClasses,
                                        MatchedPolicyClasses>::matchPolicy(
        std::forward<ParameterTuple>(params),
        current_class,
        policies ...);
    }
  }
};


/*!
 * Failure state. We did not find a policy class type for the current Policy.
 *
 * \tparam Product The class that should be created
 * \tparam AbstractProduct The base class of Product
 * \tparam RemainingPolicies The policies that would still have to be matched.
 * \tparam MatchedPolicyClasses Policy classes that have been matched before the error occurred.
 */
template <template <typename ...> class Product,
          typename AbstractProduct,
          typename RemainingPolicies,
          typename MatchedPolicyClasses>
class StaticMultiDispatchFactory<Product,
                                 AbstractProduct,
                                 RemainingPolicies,
                                 NullType,
                                 MatchedPolicyClasses>{
 public:
  template <typename ParameterTuple,
            typename PolicyClassToBeMatched,
            typename ... OtherPolicyClasses>
  static AbstractProduct* matchPolicy(ParameterTuple&&, PolicyClassToBeMatched&&,
                                      OtherPolicyClasses&& ...) {
    LOG << "Error policy not found";
    std::exit(-1);
    return nullptr;
  }
};

/*!
 * Success state. All policies have been matched. We can now use the types of
 * the matched policy classes to trigger object creation.
 *
 * \tparam Product The class that should be created
 * \tparam AbstractProduct The base class of Product
 * \tparam MatchedPolicyClasses The type of each policy class for each policy.
 */
template <template <typename ...> class Product,
          typename AbstractProduct,
          typename MatchedPolicyClasses>
class StaticMultiDispatchFactory<Product,
                                 AbstractProduct,
                                 NullType,
                                 EmptyTypelist,
                                 MatchedPolicyClasses>{
 public:
  /*!
  * Trigger object construction.
  *
  * \tparam ParameterTuple A tuple containing all parameters needed to call Product's constructor
  * \tparam PolicyClasses The concrete policy classes chosen at runtime.
  */
  template <typename ParameterTuple,
            typename ... PolicyClasses>
  static AbstractProduct* create(ParameterTuple&& params, PolicyClasses&& ...) {
    return create_impl(std::forward<ParameterTuple>(params), MatchedPolicyClasses());
  }

  /*!
  * Trigger object construction. Helper method to extract Instantiation and Parameter types.
  *
  * \tparam Parameters All parameters needed to call Product's constructor
  * \tparam Instantiations The concrete policy classes chosen at runtime.
  * \tparam T Helper to extract instantiations
  */
  template <typename ... Parameters,
            typename ... Instantiations,
            template <typename ...> class T>
  static AbstractProduct* create_impl(std::tuple<Parameters ...>&& params,
                                      T<Instantiations ...>&&) {
    return create_impl(std::tuple<Parameters ...>(params),
                       std::index_sequence_for<Parameters ...>{ }, Instantiations() ...);
  }

  /*!
  * Instantiate concrete implementation of Product with selected policies.
  *
  * \tparam Parameters All parameters needed to call Product's constructor
  * \tparam Policies The concrete policy classes chosen at runtime.
  * \tparam Is The index sequence to extract constructor parameters from tuple.
  */
  template <typename ... Parameters,
            typename ... Policies,
            std::size_t ... Is>
  static AbstractProduct* create_impl(std::tuple<Parameters ...>&& params,
                                      std::index_sequence<Is ...>,
                                      Policies&& ...) {
    return new Product<Policies ...>(
      std::get<Is>(std::tuple<Parameters ...>(params)) ...);
  }
};
}  // namespace meta
}  // namespace kahypar
