import { Dimensions, Image, View } from 'react-native';
import { createElement, useState } from 'react';
import FilledButton from './buttons/FilledButton';
import Onboarding from 'react-native-onboarding-swiper';
import TextButton from './buttons/TextButton';
import { spacing } from './util/spacing';

// based on https://github.com/jfilter/react-native-onboarding-swiper

const windowWidth = Dimensions.get('window').width;
const styles = {
  container: {
    height: '100%',
    width: '100%',
    zIndex: 10,
  },
  onboarding: { justifyContent: 'center' },
  title: {
    color: '#4B4B4B',
    fontSize: 30,
    fontWeight: '400',
    textAlign: 'left',
    width: windowWidth - spacing.regular * 2,
  },
  subTitle: {
    color: '#4B4B4B',
    fontSize: 16,
    lineHeight: 16 * 1.5,
    textAlign: 'left',
    width: windowWidth - spacing.regular * 2,
  },
  image: {
    margin: 0,
    padding: 0,
    resizeMode: 'contain',
    maxWidth: windowWidth - spacing.regular * 2,
  },
  imageContainer: {
    paddingBottom: spacing.regular,
    height: 'auto',
    width: 'auto',
  },
};

export function NativeOnboarding({
  bottombarHighlight,
  bottombarTextColor,
  currentPageDotColor,
  doneButtonColor,
  doneButtonText,
  dotColor,
  doneAction,
  doneText,
  nextText,
  pages,
  showSkip,
  skipAction,
  skipText,
}) {
  const onboardingPages = [];
  const [currentPage, setCurrentPage] = useState(0);

  const Square = ({ selected }) => {
    const backgroundColor = selected ? currentPageDotColor : 'transparent';
    const borderColor = selected ? 'transparent' : dotColor;

    return (
      <View
        style={{
          borderRadius: 20,
          borderWidth: 1,
          width: 8,
          height: 8,
          marginHorizontal: 3,
          backgroundColor,
          borderColor,
        }}
      />
    );
  };

  const Skip = ({ ...props }) => (
    <TextButton
      title={skipText}
      textColor={bottombarTextColor}
      marginLeft={spacing.regular}
      fontSize={14}
      {...props}
    />
  );

  const Next = ({ ...props }) => (
    <TextButton
      title={nextText}
      textColor={bottombarTextColor}
      marginRight={spacing.regular}
      fontSize={14}
      {...props}
    />
  );

  const Done = ({ ...props }) => (
    <FilledButton
      backgroundColor={doneButtonColor}
      title={doneText}
      textColor={doneButtonText}
      marginRight={spacing.regular}
      fontSize={14}
      {...props}
    />
  );

  function actionButton() {
    if (doneAction && doneAction.canExecute) {
      doneAction.execute();
    }
  }

  function skipButton() {
    if (skipAction && skipAction.canExecute) {
      setCurrentPage(0);
      skipAction.execute();
    }
  }

  pages.map((page) =>
    onboardingPages.push({
      backgroundColor: page.pageBackground || 'transparent',
      title: page.pageTitle || '',
      subtitle: page.pageSubTitle || '',
      image: (
        <Image
          source={Number(page.pageImage.value)}
          style={[styles.image, { height: page.pageImageSize }]}
        />
      ),
    })
  );

  return (
    <View style={styles.container}>
      <Onboarding
        allowFontScalingText={false}
        bottomBarHighlight={bottombarHighlight}
        currentPage={currentPage}
        SkipButtonComponent={Skip}
        DotComponent={Square}
        NextButtonComponent={Next}
        DoneButtonComponent={Done}
        onSkip={skipAction && skipButton}
        onDone={doneAction && actionButton}
        pages={onboardingPages}
        transitionAnimationDuration={200}
        titleStyles={styles.title}
        imageContainerStyles={styles.imageContainer}
        subTitleStyles={styles.subTitle}
        containerStyles={styles.onboarding}
        showSkip={showSkip}
      />
    </View>
  );
}
