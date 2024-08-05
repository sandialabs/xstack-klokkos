install_binary_artifact_cmake() {
  source "${DIR}/common-functions"

}

get_build_artifacts_cmake() {
  return 0
}

# Check if the binary artifact is installed
is_installed_cmake() {
  if which cmake ; then
    return 0
  fi

  return 1
}

setup_artifact_variables_cmake() {
  return 0
}